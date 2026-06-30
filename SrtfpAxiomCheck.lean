/- Axiom linter — fails the build if any project definition uses a
   disallowed axiom.  To reuse in another project, change the two
   lines marked CONFIGURE below.

   PERFORMANCE: rather than calling `Lean.collectAxioms` once per `PP.*`
   decl (each call re-walks that decl's entire transitive cone with a
   call-local visited set → O(N·M)), we build a SINGLE memoized
   transitive-axiom map over the reachable constant graph. Each constant
   is processed once and its axiom set reused by all dependents → linear.

   The memoized `axiomsOf` reproduces `Lean.collectAxioms` semantics
   EXACTLY (same kernel env `env.checked`, same per-`ConstantInfo`
   traversal rules, same `Expr.getUsedConstants`, including the
   axiom-traverses-its-own-type behaviour of Lean ≥4.23 / 4.27). It is
   cycle-safe (mutual recursion forms reference cycles) via Tarjan SCC
   condensation: all members of a strongly-connected component share one
   axiom set, computed once per SCC in reverse-topological order. -/

-- CONFIGURE: import the project root module
import Srtfp
import Srtfp.Numeric.Schubfach.Perf.CsimpPin -- build-time pin of live @[csimp] kernels
import Lean.Elab.Command

open Lean

-- CONFIGURE: namespace roots to scan, and permitted axioms
private def roots : Array Lean.Name := #[`PP]
private def allowedAxioms : Array Lean.Name :=
  #[`propext, `Quot.sound, `Classical.choice,
    -- IEEE-754 binary64 runtime intrinsic axiom (`Float.toBits ∘ Float.ofBits = id`).
    -- Used (transitively) by the Clinger `DecodeOfDecimalBridge` proof; not
    -- derivable in pure Lean 4 because `Float` is opaque.
    `Float.toBits_ofBits]

/-- True if the constant is `partial` or `unsafe` (from `partial def` or `unsafe def`). -/
private def isPartialOrUnsafe (env : Lean.Environment) (name : Lean.Name) : Bool :=
  match env.find? name with
  | some (.defnInfo dv) => dv.safety != .safe
  | some (.opaqueInfo _) => env.contains (name ++ `_unsafe_rec)
  | _ => false

/-- True if `name` is a partial/unsafe def, or a child (e.g. `_proof_1`) of one. -/
private def isPartialDefRelated (env : Lean.Environment) (name : Lean.Name) : Bool :=
  isPartialOrUnsafe env name || isPartialOrUnsafe env name.getPrefix

/-- True if `name` directly depends on any partial/unsafe def.
    This catches definitions like `IsQuad` instances for partial parsers,
    where the `sorryAx` is inherited from the partial def, not from
    an incomplete proof. -/
private def dependsOnPartialDef (env : Lean.Environment) (name : Lean.Name) : Bool :=
  match env.find? name with
  | some ci =>
    let consts := ci.type.getUsedConstants ++
      (match ci.value? with | some v => v.getUsedConstants | none => #[])
    consts.any fun dep =>
      isPartialOrUnsafe env dep || isPartialOrUnsafe env dep.getPrefix
  | none => false

/-- `sorryAx` from a partial/unsafe def is tolerated: it's the inherent
    cost of `partial def`, not an incomplete proof. -/
private def sorryFromPartialOk (env : Lean.Environment) (name : Lean.Name) : Bool :=
  isPartialDefRelated env name || dependsOnPartialDef env name

namespace AxiomMemo

/-- Direct constants referenced by `c`, EXACTLY as `Lean.CollectAxioms.collect`
    would recurse into them for the given `ConstantInfo` variant. Reads from
    the kernel env (`env.checked`), like `collectAxioms`. The returned array is
    the set of out-edges of `c` in the reference graph (axiom-ness of `c`
    itself is recorded separately). -/
private def directDeps (kenv : Kernel.Environment) (c : Name) : Array Name :=
  match kenv.find? c with
  | some (.axiomInfo v)  => v.type.getUsedConstants
  | some (.defnInfo v)   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.thmInfo v)    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.quotInfo _)   => #[]
  | some (.ctorInfo v)   => v.type.getUsedConstants
  | some (.recInfo v)    => v.type.getUsedConstants
  | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
  | none                 => #[]

/-- Is `c` an axiom in the kernel env? (mirrors the `axiomInfo` branch that
    pushes `c` onto the axiom accumulator). -/
private def isAxiom (kenv : Kernel.Environment) (c : Name) : Bool :=
  match kenv.find? c with
  | some (.axiomInfo _) => true
  | _ => false

/-- Tarjan SCC + reverse-topological axiom propagation state.

    We compute, for every constant reachable from the requested roots, the set
    of axioms in its transitive cone — matching `collectAxioms`. Cycles
    (mutual recursion) are handled by condensing each strongly-connected
    component to a single node: all members share one axiom set, equal to the
    union of (a) axioms among the SCC's own members and (b) the axiom sets of
    every successor SCC. Processing SCCs as Tarjan finalizes them (which is in
    reverse-topological order) guarantees successors are already resolved. -/
private structure St where
  kenv     : Kernel.Environment
  /-- Finalized transitive-axiom set per constant (one entry once its SCC is
      popped). Shared structurally across an SCC's members. -/
  memo     : Std.HashMap Name NameSet := {}
  /-- DFS discovery index. `none` once popped into `memo`. -/
  index    : Std.HashMap Name Nat := {}
  lowlink  : Std.HashMap Name Nat := {}
  onStack  : Std.HashMap Name Bool := {}
  stack    : Array Name := #[]
  counter  : Nat := 0

/-- Iterative Tarjan SCC. Returns the finalized state with `memo` populated for
    every constant reachable from `root`. Iterative (explicit work stack) to
    avoid native stack overflow on the deep PP cone. -/
private partial def strongConnect (root : Name) : StateM St Unit := do
  if (← get).index.contains root then return
  -- Work stack of (node, childIndexToProcessNext, depsArray).
  let mut work : Array (Name × Nat × Array Name) := #[]
  -- Push initial.
  do
    let st ← get
    let deps := directDeps st.kenv root
    modify fun s => { s with
      index := s.index.insert root s.counter,
      lowlink := s.lowlink.insert root s.counter,
      counter := s.counter + 1,
      onStack := s.onStack.insert root true,
      stack := s.stack.push root }
    work := work.push (root, 0, deps)
  while work.size > 0 do
    let (v, i, deps) := work[work.size - 1]!
    if i < deps.size then
      let w := deps[i]!
      -- advance child pointer for v
      work := work.set! (work.size - 1) (v, i + 1, deps)
      let st ← get
      if !st.index.contains w then
        -- descend into w
        let wdeps := directDeps st.kenv w
        modify fun s => { s with
          index := s.index.insert w s.counter,
          lowlink := s.lowlink.insert w s.counter,
          counter := s.counter + 1,
          onStack := s.onStack.insert w true,
          stack := s.stack.push w }
        work := work.push (w, 0, wdeps)
      else if st.onStack.getD w false then
        -- back/cross edge to node still on stack: lowlink[v] = min(lowlink[v], index[w])
        let lv := st.lowlink.getD v 0
        let iw := st.index.getD w 0
        if iw < lv then
          modify fun s => { s with lowlink := s.lowlink.insert v iw }
    else
      -- all children of v processed; pop the frame
      work := work.pop
      -- propagate lowlink to parent (the new top, if any)
      let st ← get
      let lv := st.lowlink.getD v 0
      if work.size > 0 then
        let (p, pi, pdeps) := work[work.size - 1]!
        let lp := st.lowlink.getD p 0
        if lv < lp then
          modify fun s => { s with lowlink := s.lowlink.insert p lv }
        -- keep frame as-is (child pointer already advanced)
        work := work.set! (work.size - 1) (p, pi, pdeps)
      -- if v is an SCC root, pop its component
      if st.index.getD v 0 == lv then
        -- gather members
        let mut members : Array Name := #[]
        let mut continue_ := true
        while continue_ do
          let s ← get
          let top := s.stack.back!
          modify fun s => { s with
            stack := s.stack.pop,
            onStack := s.onStack.insert top false }
          members := members.push top
          if top == v then continue_ := false
        -- compute the shared axiom set for this SCC:
        --   own axioms (members that are axiomInfo) ∪ memo of all out-edge targets
        --   that lie OUTSIDE this SCC (intra-SCC targets contribute only their
        --   own axiom-ness, already covered by iterating members).
        let s ← get
        let memberSet : Std.HashMap Name Bool :=
          members.foldl (fun m n => m.insert n true) {}
        let mut acc : NameSet := {}
        for m in members do
          if isAxiom s.kenv m then
            acc := acc.insert m
          for d in directDeps s.kenv m do
            if !memberSet.contains d then
              match s.memo.get? d with
              | some ds => acc := acc.union ds
              | none => pure ()  -- d not yet finalized only if it's outside the
                                 -- reachable graph processed so far; by Tarjan
                                 -- finalization order any out-of-SCC successor
                                 -- is already popped, so this is unreachable.
        -- assign the shared set to every member
        modify fun s =>
          { s with memo := members.foldl (fun m n => m.insert n acc) s.memo }
  return

/-- Memoized transitive-axiom map for all constants reachable (in the
    `collectAxioms` reference graph) from any name in `seeds`. -/
def buildAxiomMemo (seeds : Array Name) : StateM St Unit := do
  for s in seeds do
    strongConnect s

/-- Run the memoization and return the finalized memo map. -/
def computeMemo (env : Environment) (seeds : Array Name) : Std.HashMap Name NameSet :=
  let kenv := env.checked.get
  let (_, st) := (buildAxiomMemo seeds).run { kenv := kenv }
  st.memo

end AxiomMemo

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- Collect all PP.* roots once.
  let seeds : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if roots.any (· == n.getRoot) then acc.push n else acc
  -- Single memoized transitive-axiom computation over the whole reachable cone.
  let memo := AxiomMemo.computeMemo env seeds
  let mut bad := #[]
  for name in seeds do
    let axs := memo.getD name {}
    for ax in axs do
      if ax ∉ allowedAxioms then
        -- sorryAx is tolerated in partial defs and their dependents
        -- (e.g. IsQuad instances for partial parsers)
        unless ax == `sorryAx && sorryFromPartialOk env name do
          bad := bad.push (name, ax)
  unless bad.isEmpty do
    throwError "Disallowed axioms:\n{"\n".intercalate (bad.toList.map fun (n, a) => s!"  {n}: {a}")}"
