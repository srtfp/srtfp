/- Minimal core-only stand-ins for the Mathlib tactic surface this library
   uses, introduced when the Mathlib dependency was dropped. Each covers
   exactly the usage patterns found in this repo, not the full Mathlib
   feature set. -/

/-- Core-only replacement for the fragment of Mathlib's `push_neg` this
    library uses: negations of arithmetic comparisons and double negation.
    Implemented as a simp set, so shapes it doesn't know are left alone
    (and the call fails if nothing changes, same as the original). -/
syntax "push_neg" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| push_neg $[$loc:location]?) =>
    `(tactic| simp only [Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le,
        Rat.not_lt, Rat.not_le, Decidable.not_not, ne_eq,
        Classical.not_forall, Classical.not_imp, not_exists, not_or] $[$loc:location]?)

/-- Core-only `by_contra`: prove the goal by refuting its negation
    (classically). -/
macro "by_contra" h:ident : tactic =>
  `(tactic| (apply Classical.byContradiction; intro $h:ident))

/-- Core-only replacement for Mathlib's `set` tactic (the subset used in this
    library): introduce `x` as a local definition for `e`, rewrite occurrences
    of `e` in the goal to `x`, and (with `with h`) record `h : x = e`. Unlike
    Mathlib's `set`, hypotheses are never rewritten. -/
syntax "set " ident (" : " term)? " := " term (" with " ident)? : tactic

macro_rules
  | `(tactic| set $x:ident := $e:term) =>
    `(tactic| (let $x : _ := $e; try rw [show $e = $x from rfl] at *))
  | `(tactic| set $x:ident := $e:term with $h:ident) =>
    `(tactic| (let $x : _ := $e; try rw [show $e = $x from rfl] at *;
               have $h : $x = $e := rfl))
  | `(tactic| set $x:ident : $t:term := $e:term) =>
    `(tactic| (let $x : $t := $e; try rw [show $e = $x from rfl] at *))
  | `(tactic| set $x:ident : $t:term := $e:term with $h:ident) =>
    `(tactic| (let $x : $t := $e; try rw [show $e = $x from rfl] at *;
               have $h : $x = $e := rfl))

/-- Core-only approximation of Mathlib's `split_ifs`: exhaustively split
    every `if` in the goal. Hypothesis-naming (`with h`) is not supported;
    the sites in this repo don't use it. -/
macro "split_ifs" : tactic => `(tactic| repeat' split)
