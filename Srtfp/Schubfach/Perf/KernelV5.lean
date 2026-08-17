/- Kernel v5: erase the binary64 domain re-check from the hot path.

   `shiftedSig_v4` re-establishes its domain predicate
   `0 < m ∧ m < 2^53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q`
   at runtime on every call.  That check is expensive in compiled code:
   the `2^53` literal lowers to a per-call `lean_cstr_to_nat` decimal
   string parse (Lean's C backend emits literals above `2^32` as string
   parses, and this one sits in a position the literal-lifting pass does
   not reach), and `kOfMQ` (the spec form) is recomputed and compared.
   Callgrind: ~21% of kernel instructions.

   Every caller already holds all five facts as `dite` binders, so v5
   passes them as a hypothesis instead — erased at runtime, certified at
   compile time. -/
import Srtfp.Schubfach.Perf.Kernel192Correctness

namespace Srtfp.Schubfach

/-- `shiftedSig_v4` with the binary64-domain check as a hypothesis.
    The width guards stay (cheap `Int` compares); `m < 2^60` is implied
    by the hypothesis. -/
@[inline]
def shiftedSig_v4c (m : Nat) (q : Int) (k : Int)
    (_h_dom : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q) : Nat :=
  let sigTuple := pow10Lookup192 (-k)
  let sigGHi := sigTuple.1
  let sigGMid := sigTuple.2.1
  let sigGLo := sigTuple.2.2.1
  let sigH := sigTuple.2.2.2
  let sigShiftAmt : Int := sigH - q
  if _h_k_lo : (-k : Int) < pow10Table192_kMin then shiftedSig m q k
  else if _h_k_hi : (-k : Int) > pow10Table192_kMax then shiftedSig m q k
  else if _h_s_lo : sigShiftAmt < 188 then shiftedSig m q k
  else if _h_s_hi : sigShiftAmt ≥ 256 then shiftedSig m q k
  else
    let mU : UInt64 := UInt64.ofNat m
    let shiftAmtU : UInt64 := UInt64.ofNat sigShiftAmt.toNat
    (shiftedSig_u192_kernel mU sigGHi sigGMid sigGLo shiftAmtU).toNat

theorem shiftedSig_v4c_eq (m : Nat) (q k : Int)
    (h : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q) :
    shiftedSig_v4c m q k h = shiftedSig_v4 m q k := by
  obtain ⟨h0, h53, hq_lo, hq_hi, hk⟩ := h
  unfold shiftedSig_v4c shiftedSig_v4
  rw [dif_neg (by omega : ¬ m ≥ (1 <<< 60 : Nat))]
  by_cases h_k_lo : (-k : Int) < pow10Table192_kMin
  · simp only [dif_pos h_k_lo]
  simp only [dif_neg h_k_lo]
  by_cases h_k_hi : (-k : Int) > pow10Table192_kMax
  · simp only [dif_pos h_k_hi]
  simp only [dif_neg h_k_hi]
  by_cases h_s_lo : ((pow10Lookup192 (-k)).2.2.2 - q) < 188
  · simp only [dif_pos h_s_lo]
  simp only [dif_neg h_s_lo]
  by_cases h_s_hi : ((pow10Lookup192 (-k)).2.2.2 - q) ≥ 256
  · simp only [dif_pos h_s_hi]
  simp only [dif_neg h_s_hi]
  rw [dif_pos ⟨h0, h53, hq_lo, hq_hi, hk⟩]

/-- `shortestUnsigned_u64_opt_v3` with a leading `m = 0` guard (one
    scalar compare) so the binary64-domain facts are available as
    hypotheses for `shiftedSig_v4c`. -/
@[inline]
def shortestUnsigned_u64_opt_v4 (m : Nat) (q : Int) : Option (UInt64 × Int) :=
  if h_m0 : m = 0 then none
  else if h_m : m ≥ (1 <<< 53 : Nat) then none
  else if h_q_lo : q < (-1074 : Int) then none
  else if h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    if h_k_lo : k < pow10Table128_kMin then none
    else if h_k_hi : k + 1 > pow10Table128_kMax then none
    else
      let s := shiftedSig_v4c m q k
        ⟨Nat.pos_of_ne_zero h_m0, by omega, by omega, by omega, kOfMQ_fast_eq m q⟩
      if h_s : s ≥ (1 <<< 57 : Nat) then none
      else
        let sU : UInt64 := UInt64.ofNat s
        let mU : UInt64 := UInt64.ofNat m
        if sU ≥ (10 : UInt64) then
          let kHigh : Int := k + 1
          let cmpTupleH := pow10Lookup128 kHigh
          let cmpHGHi := cmpTupleH.1
          let cmpHGLo := cmpTupleH.2.1
          let cmpHH := cmpTupleH.2.2
          let cmpHQPlusH : Int := q + cmpHH
          if h_qh_lo : cmpHQPlusH < 64 then none
          else if h_qh_hi : cmpHQPlusH > 132 then none
          else
            let cmpHQPlusH8 : UInt64 := UInt64.ofNat cmpHQPlusH.toNat
            let sHighU : UInt64 := sU / 10
            let uV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                        sHighU mU irregular
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, kHigh)
            else
              let wV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                          (sHighU + 1) mU irregular
              if wV = inRoundingInterval_u8_AMBIG then none
              else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, kHigh)
              else
                let cmpTuple := pow10Lookup128 k
                let cmpGHi := cmpTuple.1
                let cmpGLo := cmpTuple.2.1
                let cmpH := cmpTuple.2.2
                let cmpQPlusH : Int := q + cmpH
                if h_qh2_lo : cmpQPlusH < 64 then none
                else if h_qh2_hi : cmpQPlusH > 132 then none
                else
                  let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
                  match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
                  | none => none
                  | some chosen => some (chosen, k)
        else if h_s1 : sU = 0 then none
        else
          let cmpTuple := pow10Lookup128 k
          let cmpGHi := cmpTuple.1
          let cmpGLo := cmpTuple.2.1
          let cmpH := cmpTuple.2.2
          let cmpQPlusH : Int := q + cmpH
          if h_qh2_lo : cmpQPlusH < 64 then none
          else if h_qh2_hi : cmpQPlusH > 132 then none
          else
            let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
            match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
            | none => none
            | some chosen => some (chosen, k)

theorem shortestUnsigned_u64_opt_v4_eq_v3 (m : Nat) (q : Int) (h_m0 : m ≠ 0) :
    shortestUnsigned_u64_opt_v4 m q = shortestUnsigned_u64_opt_v3 m q := by
  unfold shortestUnsigned_u64_opt_v4 shortestUnsigned_u64_opt_v3
  rw [dif_neg h_m0]
  simp only [shiftedSig_v4c_eq]
  rfl

@[inline]
def shortestUnsigned_v5 (m : Nat) (q : Int) : Nat × Int :=
  match shortestUnsigned_u64_opt_v4 m q with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed m q

theorem shortestUnsigned_v5_eq (m : Nat) (q : Int) :
    shortestUnsigned_v5 m q = shortestUnsigned m q := by
  unfold shortestUnsigned_v5
  by_cases h_m0 : m = 0
  · subst h_m0
    rw [show shortestUnsigned_u64_opt_v4 0 q = none from by
          unfold shortestUnsigned_u64_opt_v4; rw [dif_pos rfl]]
    exact shortestUnsigned_packed_eq 0 q
  · rw [shortestUnsigned_u64_opt_v4_eq_v3 m q h_m0]
    show shortestUnsigned_v4 m q = shortestUnsigned m q
    exact shortestUnsigned_v4_eq m q

end Srtfp.Schubfach
