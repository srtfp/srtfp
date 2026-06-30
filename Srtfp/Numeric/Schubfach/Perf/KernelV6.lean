/- Kernel v6a: one biased table index, no dead guards.

   The v4/v5 hot path computes a table index from `k : Int` three times
   per call (`-k+324`, `k+1+324`, `k+324`), each through boxed `Int`
   negation/addition plus an `Int.toNat` call, and re-checks 192-table
   range guards that the 128-table guards already imply.  v6 computes
   `kB := (k + 324).toNat` once; every lookup becomes scalar `Nat`
   index arithmetic (`648 - kB`, `kB + 1`, `kB`), and the implied
   guards are gone (their falsity is proven, not re-tested). -/
import Srtfp.Numeric.Schubfach.Perf.KernelV5

namespace PP.Numeric.Schubfach

@[inline]
def shortestUnsigned_u64_opt_v6 (m : Nat) (q : Int) : Option (UInt64 × Int) :=
  if _h_m0 : m = 0 then none
  else if _h_m : m ≥ (1 <<< 53 : Nat) then none
  else if _h_q_lo : q < (-1074 : Int) then none
  else if _h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    if _h_k_lo : k < pow10Table128_kMin then none
    else if _h_k_hi : k + 1 > pow10Table128_kMax then none
    else
      let kB : Nat := (k + 324).toNat
      let sigTuple := pow10Table192.getD (648 - kB) pow10Table192_default
      let sigShiftAmt : Int := sigTuple.2.2.2 - q
      let s : Nat :=
        if _h_s_lo : sigShiftAmt < 188 then shiftedSig m q k
        else if _h_s_hi : sigShiftAmt ≥ 256 then shiftedSig m q k
        else
          let mU : UInt64 := UInt64.ofNat m
          let shiftAmtU : UInt64 := UInt64.ofNat sigShiftAmt.toNat
          (shiftedSig_u192_kernel mU sigTuple.1 sigTuple.2.1 sigTuple.2.2.1
            shiftAmtU).toNat
      if _h_s : s ≥ (1 <<< 57 : Nat) then none
      else
        let sU : UInt64 := UInt64.ofNat s
        let mU : UInt64 := UInt64.ofNat m
        if sU ≥ (10 : UInt64) then
          let cmpTupleH := pow10Table128.getD (kB + 1) pow10Table128_default
          let cmpHGHi := cmpTupleH.1
          let cmpHGLo := cmpTupleH.2.1
          let cmpHH := cmpTupleH.2.2
          let cmpHQPlusH : Int := q + cmpHH
          if _h_qh_lo : cmpHQPlusH < 64 then none
          else if _h_qh_hi : cmpHQPlusH > 132 then none
          else
            let cmpHQPlusH8 : UInt64 := UInt64.ofNat cmpHQPlusH.toNat
            let sHighU : UInt64 := sU / 10
            let uV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                        sHighU mU irregular
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, k + 1)
            else
              let wV := inRoundingInterval_u64_packed_u8 cmpHGHi cmpHGLo cmpHQPlusH8
                          (sHighU + 1) mU irregular
              if wV = inRoundingInterval_u8_AMBIG then none
              else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, k + 1)
              else
                let cmpTuple := pow10Table128.getD kB pow10Table128_default
                let cmpGHi := cmpTuple.1
                let cmpGLo := cmpTuple.2.1
                let cmpH := cmpTuple.2.2
                let cmpQPlusH : Int := q + cmpH
                if _h_qh2_lo : cmpQPlusH < 64 then none
                else if _h_qh2_hi : cmpQPlusH > 132 then none
                else
                  let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
                  match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
                  | none => none
                  | some chosen => some (chosen, k)
        else if _h_s1 : sU = 0 then none
        else
          let cmpTuple := pow10Table128.getD kB pow10Table128_default
          let cmpGHi := cmpTuple.1
          let cmpGLo := cmpTuple.2.1
          let cmpH := cmpTuple.2.2
          let cmpQPlusH : Int := q + cmpH
          if _h_qh2_lo : cmpQPlusH < 64 then none
          else if _h_qh2_hi : cmpQPlusH > 132 then none
          else
            let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
            match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
            | none => none
            | some chosen => some (chosen, k)

/-! ## Equality to v4 -/

theorem lookup192_neg (k : Int) (hlo : ¬ k < pow10Table128_kMin)
    (hhi : ¬ k + 1 > pow10Table128_kMax) :
    pow10Lookup192 (-k) = pow10Table192.getD (648 - (k + 324).toNat) pow10Table192_default := by
  have hlo' : ¬ k < (-324 : Int) := hlo
  have hhi' : ¬ k + 1 > (324 : Int) := hhi
  have hidx : (-k + 324).toNat = 648 - (k + 324).toNat := by omega
  unfold pow10Lookup192
  rw [if_neg (show ¬ (-k < pow10Table192_kMin) from
        fun hc => absurd (show k > 324 from by
          have : (-k : Int) < -324 := hc
          omega) (by omega)),
      hidx]

theorem lookup128_high (k : Int) (hlo : ¬ k < pow10Table128_kMin) :
    pow10Lookup128 (k + 1) = pow10Table128.getD ((k + 324).toNat + 1) pow10Table128_default := by
  have hlo' : ¬ k < (-324 : Int) := hlo
  have hidx : (k + 1 + 324).toNat = (k + 324).toNat + 1 := by omega
  unfold pow10Lookup128
  rw [if_neg (show ¬ (k + 1 < pow10Table128_kMin) from
        fun hc => absurd (show k + 1 < -324 from hc) (by omega)),
      hidx]

theorem lookup128_low (k : Int) (hlo : ¬ k < pow10Table128_kMin) :
    pow10Lookup128 k = pow10Table128.getD ((k + 324).toNat) pow10Table128_default := by
  unfold pow10Lookup128
  rw [if_neg hlo]

set_option maxRecDepth 16384 in
theorem shortestUnsigned_u64_opt_v6_eq_v4 (m : Nat) (q : Int) :
    shortestUnsigned_u64_opt_v6 m q = shortestUnsigned_u64_opt_v4 m q := by
  unfold shortestUnsigned_u64_opt_v6 shortestUnsigned_u64_opt_v4
  by_cases h_m0 : m = 0
  · rw [dif_pos h_m0, dif_pos h_m0]
  rw [dif_neg h_m0, dif_neg h_m0]
  by_cases h_m : m ≥ (1 <<< 53 : Nat)
  · rw [dif_pos h_m, dif_pos h_m]
  rw [dif_neg h_m, dif_neg h_m]
  by_cases h_q_lo : q < (-1074 : Int)
  · rw [dif_pos h_q_lo, dif_pos h_q_lo]
  rw [dif_neg h_q_lo, dif_neg h_q_lo]
  by_cases h_q_hi : q > 971
  · rw [dif_pos h_q_hi, dif_pos h_q_hi]
  rw [dif_neg h_q_hi, dif_neg h_q_hi]
  by_cases h_k_lo : kOfMQ_fast m q < pow10Table128_kMin
  · rw [dif_pos h_k_lo, dif_pos h_k_lo]
  rw [dif_neg h_k_lo, dif_neg h_k_lo]
  by_cases h_k_hi : kOfMQ_fast m q + 1 > pow10Table128_kMax
  · rw [dif_pos h_k_hi, dif_pos h_k_hi]
  rw [dif_neg h_k_hi, dif_neg h_k_hi]
  -- instantiated rewrite equations
  have e1 := lookup192_neg (kOfMQ_fast m q) h_k_lo h_k_hi
  have e2 := lookup128_high (kOfMQ_fast m q) h_k_lo
  have e3 := lookup128_low (kOfMQ_fast m q) h_k_lo
  -- dead 192-table range guards on the v4 side
  have hlo' : ¬ kOfMQ_fast m q < (-324 : Int) := h_k_lo
  have hhi' : ¬ kOfMQ_fast m q + 1 > (324 : Int) := h_k_hi
  have e4 : (-(kOfMQ_fast m q) < pow10Table192_kMin) = False :=
    eq_false (show ¬ (-(kOfMQ_fast m q) < (-324 : Int)) from by omega)
  have e5 : (-(kOfMQ_fast m q) > pow10Table192_kMax) = False :=
    eq_false (show ¬ (-(kOfMQ_fast m q) > (324 : Int)) from by omega)
  simp only [shiftedSig_v4c, e1, e2, e3, e4, e5, dite_false]
  rfl

@[inline]
def shortestUnsigned_v6 (m : Nat) (q : Int) : Nat × Int :=
  match shortestUnsigned_u64_opt_v6 m q with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed m q

theorem shortestUnsigned_v6_eq (m : Nat) (q : Int) :
    shortestUnsigned_v6 m q = shortestUnsigned m q := by
  unfold shortestUnsigned_v6
  rw [shortestUnsigned_u64_opt_v6_eq_v4]
  show shortestUnsigned_v5 m q = shortestUnsigned m q
  exact shortestUnsigned_v5_eq m q

theorem shortestUnsigned_v6_eq_v5 (m : Nat) (q : Int) :
    shortestUnsigned_v6 m q = shortestUnsigned_v5 m q := by
  rw [shortestUnsigned_v6_eq, shortestUnsigned_v5_eq]

/-! ## Fused `toDecimal_v6` (csimp overrides v5; later csimps win) -/

open PP.Numeric.Float in
def toDecimal_v6 (f : _root_.Float) : Except String _root_.PP.Numeric.Decimal :=
  if isNaNBits f then
    .error "NaN"
  else if isInfBits f then
    .error (if signBit f then "-Infinity" else "Infinity")
  else
    let d := decode f
    if d.m = 0 then .ok ⟨d.sign, 0, 0⟩
    else
      let (sig, exp) := shortestUnsigned_v6 d.m d.q
      .ok (PP.Numeric.Decimal.mk' d.sign sig exp)

theorem toDecimal_v6_eq (f : _root_.Float) :
    toDecimal_v6 f = toDecimal f := by
  unfold toDecimal_v6 toDecimal
  by_cases h1 : PP.Numeric.Float.isNaNBits f = true
  · simp [h1]
  by_cases h2 : PP.Numeric.Float.isInfBits f = true
  · simp [h1, h2]
  simp only [h1, h2, if_false, Bool.false_eq_true]
  by_cases h3 : (PP.Numeric.Float.decode f).m = 0
  · simp [h3]
  simp only [h3, if_false]
  rw [shortestUnsigned_v6_eq]

-- Superseded registration: `toDecimal_eq_v7_csimp` below is the live @[csimp].
theorem toDecimal_eq_v6_csimp : @toDecimal = @toDecimal_v6 := by
  funext f
  exact (toDecimal_v6_eq f).symm

/-! ## v7: pre-biased h side-tables, no Int arithmetic in the hot body

The three `h ± q` computations each cost a boxed `Int` add/sub, two
boxed compares and an `Int.toNat`.  v7 reads `h + 2048` from a scalar
side table (values < 2^12: unboxed in `Array UInt64`), carries
`qB = q + 1074` as a `UInt64`, and does all range tests and shift
amounts in wrap-safe biased `UInt64` arithmetic. -/

/-- `h + 2048` per 128-table entry (scalar-sized, unboxed reads). -/
def hB128 : Array UInt64 :=
  pow10Table128.map (fun t => UInt64.ofNat (t.2.2 + 2048).toNat)

/-- `h + 2048` per 192-table entry. -/
def hB192 : Array UInt64 :=
  pow10Table192.map (fun t => UInt64.ofNat (t.2.2.2 + 2048).toNat)

/-- All 128-table `h` values lie in `[-2048, 2048)`. -/
def hBounds128Bool : Bool :=
  (List.range pow10Table128.size).all fun i =>
    decide (-2048 ≤ (pow10Table128[i]!).2.2 ∧ (pow10Table128[i]!).2.2 < 2048)

theorem hBounds128 : hBounds128Bool = true := by decide +kernel

/-- All 192-table `h` values lie in `[-2048, 2048)`. -/
def hBounds192Bool : Bool :=
  (List.range pow10Table192.size).all fun i =>
    decide (-2048 ≤ (pow10Table192[i]!).2.2.2 ∧ (pow10Table192[i]!).2.2.2 < 2048)

theorem hBounds192 : hBounds192Bool = true := by decide +kernel

private theorem hBound128_at (i : Nat) (hi : i < pow10Table128.size) :
    -2048 ≤ (pow10Table128[i]!).2.2 ∧ (pow10Table128[i]!).2.2 < 2048 := by
  have hAll := hBounds128
  unfold hBounds128Bool at hAll
  rw [List.all_eq_true] at hAll
  exact decide_eq_true_eq.mp (hAll i (List.mem_range.mpr hi))

private theorem hBound192_at (i : Nat) (hi : i < pow10Table192.size) :
    -2048 ≤ (pow10Table192[i]!).2.2.2 ∧ (pow10Table192[i]!).2.2.2 < 2048 := by
  have hAll := hBounds192
  unfold hBounds192Bool at hAll
  rw [List.all_eq_true] at hAll
  exact decide_eq_true_eq.mp (hAll i (List.mem_range.mpr hi))

theorem hB128_getD (i : Nat) (hi : i < pow10Table128.size) :
    hB128.getD i 0
      = UInt64.ofNat (((pow10Table128.getD i pow10Table128_default).2.2 + 2048).toNat) := by
  have hsz : i < hB128.size := by unfold hB128; rw [Array.size_map]; exact hi
  rw [(Array.getElem_eq_getD 0 (h := hsz)).symm,
      (Array.getElem_eq_getD pow10Table128_default (h := hi)).symm]
  unfold hB128
  simp [Array.getElem_map]

theorem hB192_getD (i : Nat) (hi : i < pow10Table192.size) :
    hB192.getD i 0
      = UInt64.ofNat (((pow10Table192.getD i pow10Table192_default).2.2.2 + 2048).toNat) := by
  have hsz : i < hB192.size := by unfold hB192; rw [Array.size_map]; exact hi
  rw [(Array.getElem_eq_getD 0 (h := hsz)).symm,
      (Array.getElem_eq_getD pow10Table192_default (h := hi)).symm]
  unfold hB192
  simp [Array.getElem_map]


/-! ### Biased-arithmetic bridges -/

theorem toNat_qB (q : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971) :
    ((UInt64.ofNat (q + 1074).toNat).toNat : Int) = q + 1074 := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

theorem toNat_hb (h : Int) (hh : -2048 ≤ h ∧ h < 2048) :
    ((UInt64.ofNat (h + 2048).toNat).toNat : Int) = h + 2048 := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

theorem toNat_tA (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat).toNat : Int)
      = h - q + 5070 := by
  have hq := toNat_qB q h1 h2
  have hb := toNat_hb h hh
  rw [UInt64.toNat_sub, UInt64.toNat_add]
  rw [show ((4096 : UInt64)).toNat = 4096 from rfl]
  omega

theorem tA_lt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5258 : UInt64)) = (h - q < 188) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        < (5258 : UInt64)) ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((5258 : UInt64)).toNat = 5258 from rfl]
  exact propext (by omega)

theorem tA_ge (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        ≥ (5326 : UInt64)) = (h - q ≥ 256) := by
  have ht := toNat_tA q h h1 h2 hh
  rw [show (((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat)
        ≥ (5326 : UInt64)) ↔ _ from UInt64.le_iff_toNat_le,
      show ((5326 : UInt64)).toNat = 5326 from rfl]
  exact propext (by omega)

theorem tA_val (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) (hlo : ¬ h - q < 188) (hhi : ¬ h - q ≥ 256) :
    ((UInt64.ofNat (h + 2048).toNat + 4096) - UInt64.ofNat (q + 1074).toNat) - 5070
      = UInt64.ofNat (h - q).toNat := by
  have ht := toNat_tA q h h1 h2 hh
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, show ((5070 : UInt64)).toNat = 5070 from rfl]
        omega),
      show ((5070 : UInt64)).toNat = 5070 from rfl,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

theorem toNat_uBC (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat).toNat : Int)
      = q + h + 3122 := by
  have hq := toNat_qB q h1 h2
  have hb := toNat_hb h hh
  rw [UInt64.toNat_add]
  omega

theorem uBC_lt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) < (3186 : UInt64))
      = (q + h < 64) := by
  have ht := toNat_uBC q h h1 h2 hh
  rw [show ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) < (3186 : UInt64))
        ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((3186 : UInt64)).toNat = 3186 from rfl]
  exact propext (by omega)

theorem uBC_gt (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) :
    ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) > (3254 : UInt64))
      = (q + h > 132) := by
  have ht := toNat_uBC q h h1 h2 hh
  rw [show ((UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) > (3254 : UInt64))
        ↔ _ from UInt64.lt_iff_toNat_lt,
      show ((3254 : UInt64)).toNat = 3254 from rfl]
  exact propext (by omega)

theorem uBC_val (q h : Int) (h1 : ¬ q < -1074) (h2 : ¬ q > 971)
    (hh : -2048 ≤ h ∧ h < 2048) (hlo : ¬ q + h < 64) (hhi : ¬ q + h > 132) :
    (UInt64.ofNat (q + 1074).toNat + UInt64.ofNat (h + 2048).toNat) - 3122
      = UInt64.ofNat (q + h).toNat := by
  have ht := toNat_uBC q h h1 h2 hh
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, show ((3122 : UInt64)).toNat = 3122 from rfl]
        omega),
      show ((3122 : UInt64)).toNat = 3122 from rfl,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  omega

/-! ### getD-form bounds and content -/

theorem hBound128_getD (i : Nat) (hi : i < pow10Table128.size) :
    -2048 ≤ (pow10Table128.getD i pow10Table128_default).2.2
      ∧ (pow10Table128.getD i pow10Table128_default).2.2 < 2048 := by
  have h := hBound128_at i hi
  rwa [show pow10Table128[i]! = pow10Table128.getD i pow10Table128_default from
        Array.getElem!_eq_getD] at h

theorem hBound192_getD (i : Nat) (hi : i < pow10Table192.size) :
    -2048 ≤ (pow10Table192.getD i pow10Table192_default).2.2.2
      ∧ (pow10Table192.getD i pow10Table192_default).2.2.2 < 2048 := by
  have h := hBound192_at i hi
  rwa [show pow10Table192[i]! = pow10Table192.getD i pow10Table192_default from
        Array.getElem!_eq_getD] at h

/-! ### v7 -/

@[inline]
def shortestUnsigned_u64_opt_v7 (m : Nat) (q : Int) : Option (UInt64 × Int) :=
  if _h_m0 : m = 0 then none
  else if _h_m : m ≥ (1 <<< 53 : Nat) then none
  else if _h_q_lo : q < (-1074 : Int) then none
  else if _h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    if _h_k_lo : k < pow10Table128_kMin then none
    else if _h_k_hi : k + 1 > pow10Table128_kMax then none
    else
      let kB : Nat := (k + 324).toNat
      let qB : UInt64 := UInt64.ofNat (q + 1074).toNat
      let sigTuple := pow10Table192.getD (648 - kB) pow10Table192_default
      let tA : UInt64 := (hB192.getD (648 - kB) 0 + 4096) - qB
      let s : Nat :=
        if _h_s_lo : tA < 5258 then shiftedSig m q k
        else if _h_s_hi : tA ≥ 5326 then shiftedSig m q k
        else
          (shiftedSig_u192_kernel (UInt64.ofNat m) sigTuple.1 sigTuple.2.1
            sigTuple.2.2.1 (tA - 5070)).toNat
      if _h_s : s ≥ (1 <<< 57 : Nat) then none
      else
        let sU : UInt64 := UInt64.ofNat s
        let mU : UInt64 := UInt64.ofNat m
        if sU ≥ (10 : UInt64) then
          let cmpTupleH := pow10Table128.getD (kB + 1) pow10Table128_default
          let uB : UInt64 := qB + hB128.getD (kB + 1) 0
          if _h_qh_lo : uB < 3186 then none
          else if _h_qh_hi : uB > 3254 then none
          else
            let cmpHQPlusH8 : UInt64 := uB - 3122
            let sHighU : UInt64 := sU / 10
            let uV := inRoundingInterval_u64_packed_u8 cmpTupleH.1 cmpTupleH.2.1
                        cmpHQPlusH8 sHighU mU irregular
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, k + 1)
            else
              let wV := inRoundingInterval_u64_packed_u8 cmpTupleH.1 cmpTupleH.2.1
                          cmpHQPlusH8 (sHighU + 1) mU irregular
              if wV = inRoundingInterval_u8_AMBIG then none
              else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, k + 1)
              else
                let cmpTuple := pow10Table128.getD kB pow10Table128_default
                let uC : UInt64 := qB + hB128.getD kB 0
                if _h_qh2_lo : uC < 3186 then none
                else if _h_qh2_hi : uC > 3254 then none
                else
                  let cmpQPlusH8 : UInt64 := uC - 3122
                  match pickNearer_u64_opt cmpTuple.1 cmpTuple.2.1 cmpQPlusH8 sU mU irregular with
                  | none => none
                  | some chosen => some (chosen, k)
        else if _h_s1 : sU = 0 then none
        else
          let cmpTuple := pow10Table128.getD kB pow10Table128_default
          let uC : UInt64 := qB + hB128.getD kB 0
          if _h_qh2_lo : uC < 3186 then none
          else if _h_qh2_hi : uC > 3254 then none
          else
            let cmpQPlusH8 : UInt64 := uC - 3122
            match pickNearer_u64_opt cmpTuple.1 cmpTuple.2.1 cmpQPlusH8 sU mU irregular with
            | none => none
            | some chosen => some (chosen, k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
theorem shortestUnsigned_u64_opt_v7_eq_v6 (m : Nat) (q : Int) :
    shortestUnsigned_u64_opt_v7 m q = shortestUnsigned_u64_opt_v6 m q := by
  unfold shortestUnsigned_u64_opt_v7 shortestUnsigned_u64_opt_v6
  by_cases h_m0 : m = 0
  · rw [dif_pos h_m0, dif_pos h_m0]
  rw [dif_neg h_m0, dif_neg h_m0]
  by_cases h_m : m ≥ (1 <<< 53 : Nat)
  · rw [dif_pos h_m, dif_pos h_m]
  rw [dif_neg h_m, dif_neg h_m]
  by_cases h_q_lo : q < (-1074 : Int)
  · rw [dif_pos h_q_lo, dif_pos h_q_lo]
  rw [dif_neg h_q_lo, dif_neg h_q_lo]
  by_cases h_q_hi : q > 971
  · rw [dif_pos h_q_hi, dif_pos h_q_hi]
  rw [dif_neg h_q_hi, dif_neg h_q_hi]
  by_cases h_k_lo : kOfMQ_fast m q < pow10Table128_kMin
  · rw [dif_pos h_k_lo, dif_pos h_k_lo]
  rw [dif_neg h_k_lo, dif_neg h_k_lo]
  by_cases h_k_hi : kOfMQ_fast m q + 1 > pow10Table128_kMax
  · rw [dif_pos h_k_hi, dif_pos h_k_hi]
  rw [dif_neg h_k_hi, dif_neg h_k_hi]
  -- index bounds
  have hklo' : ¬ kOfMQ_fast m q < (-324 : Int) := h_k_lo
  have hkhi' : ¬ kOfMQ_fast m q + 1 > (324 : Int) := h_k_hi
  have hkB : (kOfMQ_fast m q + 324).toNat ≤ 647 := by omega
  have hi192 : 648 - (kOfMQ_fast m q + 324).toNat < pow10Table192.size := by
    rw [pow10Table192_size_eq]; omega
  have hi128h : (kOfMQ_fast m q + 324).toNat + 1 < pow10Table128.size := by
    rw [pow10Table128_size_eq]; omega
  have hi128l : (kOfMQ_fast m q + 324).toNat < pow10Table128.size := by
    rw [pow10Table128_size_eq]; omega
  -- h bounds at the three entries
  have hh192 := hBound192_getD _ hi192
  have hh128h := hBound128_getD _ hi128h
  have hh128l := hBound128_getD _ hi128l
  -- content equations for the biased side tables
  have c192 := hB192_getD _ hi192
  have c128h := hB128_getD _ hi128h
  have c128l := hB128_getD _ hi128l
  simp only [c192, c128h, c128l,
    tA_lt q _ h_q_lo h_q_hi hh192, tA_ge q _ h_q_lo h_q_hi hh192,
    uBC_lt q _ h_q_lo h_q_hi hh128h, uBC_gt q _ h_q_lo h_q_hi hh128h,
    uBC_lt q _ h_q_lo h_q_hi hh128l, uBC_gt q _ h_q_lo h_q_hi hh128l]
  -- descend the A-site (shift amount), then B/C sites, unifying values
  by_cases ha1 : (pow10Table192.getD (648 - (kOfMQ_fast m q + 324).toNat)
      pow10Table192_default).2.2.2 - q < 188
  case pos =>
    simp only [dif_pos ha1]
    by_cases hb1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat + 1)
        pow10Table128_default).2.2 < 64
    case pos =>
      simp only [dif_pos hb1]
      by_cases hc1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
          pow10Table128_default).2.2 < 64
      case pos => simp only [dif_pos hc1]
      case neg =>
        by_cases hc2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
            pow10Table128_default).2.2 > 132
        case pos => simp only [dif_neg hc1, dif_pos hc2]
        case neg => simp only [dif_neg hc1, dif_neg hc2,
                      uBC_val q _ h_q_lo h_q_hi hh128l hc1 hc2]
    case neg =>
      by_cases hb2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat + 1)
          pow10Table128_default).2.2 > 132
      case pos =>
        simp only [dif_neg hb1, dif_pos hb2]
        by_cases hc1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
            pow10Table128_default).2.2 < 64
        case pos => simp only [dif_pos hc1]
        case neg =>
          by_cases hc2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
              pow10Table128_default).2.2 > 132
          case pos => simp only [dif_neg hc1, dif_pos hc2]
          case neg => simp only [dif_neg hc1, dif_neg hc2,
                        uBC_val q _ h_q_lo h_q_hi hh128l hc1 hc2]
      case neg =>
        simp only [dif_neg hb1, dif_neg hb2,
          uBC_val q _ h_q_lo h_q_hi hh128h hb1 hb2]
        by_cases hc1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
            pow10Table128_default).2.2 < 64
        case pos => simp only [dif_pos hc1]
        case neg =>
          by_cases hc2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
              pow10Table128_default).2.2 > 132
          case pos => simp only [dif_neg hc1, dif_pos hc2]
          case neg => simp only [dif_neg hc1, dif_neg hc2,
                        uBC_val q _ h_q_lo h_q_hi hh128l hc1 hc2]
  case neg =>
    by_cases ha2 : (pow10Table192.getD (648 - (kOfMQ_fast m q + 324).toNat)
        pow10Table192_default).2.2.2 - q ≥ 256
    case pos =>
      simp only [dif_neg ha1, dif_pos ha2]
      by_cases hb1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat + 1)
          pow10Table128_default).2.2 < 64
      case pos =>
        simp only [dif_pos hb1]
        by_cases hc1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
            pow10Table128_default).2.2 < 64
        case pos => simp only [dif_pos hc1]
        case neg =>
          by_cases hc2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
              pow10Table128_default).2.2 > 132
          case pos => simp only [dif_neg hc1, dif_pos hc2]
          case neg => simp only [dif_neg hc1, dif_neg hc2,
                        uBC_val q _ h_q_lo h_q_hi hh128l hc1 hc2]
      case neg =>
        by_cases hb2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat + 1)
            pow10Table128_default).2.2 > 132
        case pos =>
          simp only [dif_neg hb1, dif_pos hb2]
          by_cases hc1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
              pow10Table128_default).2.2 < 64
          case pos => simp only [dif_pos hc1]
          case neg =>
            by_cases hc2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
                pow10Table128_default).2.2 > 132
            case pos => simp only [dif_neg hc1, dif_pos hc2]
            case neg => simp only [dif_neg hc1, dif_neg hc2,
                          uBC_val q _ h_q_lo h_q_hi hh128l hc1 hc2]
        case neg =>
          simp only [dif_neg hb1, dif_neg hb2,
            uBC_val q _ h_q_lo h_q_hi hh128h hb1 hb2]
          by_cases hc1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
              pow10Table128_default).2.2 < 64
          case pos => simp only [dif_pos hc1]
          case neg =>
            by_cases hc2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
                pow10Table128_default).2.2 > 132
            case pos => simp only [dif_neg hc1, dif_pos hc2]
            case neg => simp only [dif_neg hc1, dif_neg hc2,
                          uBC_val q _ h_q_lo h_q_hi hh128l hc1 hc2]
    case neg =>
      simp only [dif_neg ha1, dif_neg ha2,
        tA_val q _ h_q_lo h_q_hi hh192 ha1 ha2]
      by_cases hb1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat + 1)
          pow10Table128_default).2.2 < 64
      case pos =>
        simp only [dif_pos hb1]
        by_cases hc1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
            pow10Table128_default).2.2 < 64
        case pos => simp only [dif_pos hc1]
        case neg =>
          by_cases hc2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
              pow10Table128_default).2.2 > 132
          case pos => simp only [dif_neg hc1, dif_pos hc2]
          case neg => simp only [dif_neg hc1, dif_neg hc2,
                        uBC_val q _ h_q_lo h_q_hi hh128l hc1 hc2]
      case neg =>
        by_cases hb2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat + 1)
            pow10Table128_default).2.2 > 132
        case pos =>
          simp only [dif_neg hb1, dif_pos hb2]
          by_cases hc1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
              pow10Table128_default).2.2 < 64
          case pos => simp only [dif_pos hc1]
          case neg =>
            by_cases hc2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
                pow10Table128_default).2.2 > 132
            case pos => simp only [dif_neg hc1, dif_pos hc2]
            case neg => simp only [dif_neg hc1, dif_neg hc2,
                          uBC_val q _ h_q_lo h_q_hi hh128l hc1 hc2]
        case neg =>
          simp only [dif_neg hb1, dif_neg hb2,
            uBC_val q _ h_q_lo h_q_hi hh128h hb1 hb2]
          by_cases hc1 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
              pow10Table128_default).2.2 < 64
          case pos => simp only [dif_pos hc1]
          case neg =>
            by_cases hc2 : q + (pow10Table128.getD ((kOfMQ_fast m q + 324).toNat)
                pow10Table128_default).2.2 > 132
            case pos => simp only [dif_neg hc1, dif_pos hc2]
            case neg => simp only [dif_neg hc1, dif_neg hc2,
                          uBC_val q _ h_q_lo h_q_hi hh128l hc1 hc2]

@[inline]
def shortestUnsigned_v7 (m : Nat) (q : Int) : Nat × Int :=
  match shortestUnsigned_u64_opt_v7 m q with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed m q

theorem shortestUnsigned_v7_eq (m : Nat) (q : Int) :
    shortestUnsigned_v7 m q = shortestUnsigned m q := by
  unfold shortestUnsigned_v7
  rw [shortestUnsigned_u64_opt_v7_eq_v6]
  show shortestUnsigned_v6 m q = shortestUnsigned m q
  exact shortestUnsigned_v6_eq m q

theorem shortestUnsigned_v7_eq_v5 (m : Nat) (q : Int) :
    shortestUnsigned_v7 m q = shortestUnsigned_v5 m q := by
  rw [shortestUnsigned_v7_eq, shortestUnsigned_v5_eq]

/-! ## Fused `toDecimal_v7` (csimp overrides v6; later csimps win) -/

open PP.Numeric.Float in
def toDecimal_v7 (f : _root_.Float) : Except String _root_.PP.Numeric.Decimal :=
  if isNaNBits f then
    .error "NaN"
  else if isInfBits f then
    .error (if signBit f then "-Infinity" else "Infinity")
  else
    let d := decode f
    if d.m = 0 then .ok ⟨d.sign, 0, 0⟩
    else
      let (sig, exp) := shortestUnsigned_v7 d.m d.q
      .ok (PP.Numeric.Decimal.mk' d.sign sig exp)

theorem toDecimal_v7_eq (f : _root_.Float) :
    toDecimal_v7 f = toDecimal f := by
  unfold toDecimal_v7 toDecimal
  by_cases h1 : PP.Numeric.Float.isNaNBits f = true
  · simp [h1]
  by_cases h2 : PP.Numeric.Float.isInfBits f = true
  · simp [h1, h2]
  simp only [h1, h2, if_false, Bool.false_eq_true]
  by_cases h3 : (PP.Numeric.Float.decode f).m = 0
  · simp [h3]
  simp only [h3, if_false]
  rw [shortestUnsigned_v7_eq]

@[csimp]
theorem toDecimal_eq_v7_csimp : @toDecimal = @toDecimal_v7 := by
  funext f
  exact (toDecimal_v7_eq f).symm

/-! ## v8: all-UInt64 interface

The kernel still receives `m : Nat` and `q : Int`, re-boxes `q + 1074`
(already available as a scalar in the caller), range-checks `q` twice,
runs `kOfMQ_fast`'s Int wrapper, and converts `k + 324` to `Nat`.  v8
takes `(mU, qB) : UInt64 x UInt64` straight from the bit fields, uses a
biased `kOfMQ` that never leaves `UInt64`, and folds each guard pair
into one unsigned compare. -/

@[inline]
def floorLog10Pow2B (qB : UInt64) : UInt64 :=
  asrUInt64_41 (qB * constC_u64 - bias1074constC_u64) + 324

@[inline]
def floorLog10ThreeQuartersPow2B (qB : UInt64) : UInt64 :=
  asrUInt64_41 (qB * constC_u64 - bias1074constC_minus_constA_u64) + 324

@[inline]
def isIrregularB (mU qB : UInt64) : Bool :=
  mU = (4503599627370496 : UInt64) && qB ≥ 1

@[inline]
def kBOfMQ (mU qB : UInt64) : UInt64 :=
  if isIrregularB mU qB then floorLog10ThreeQuartersPow2B qB else floorLog10Pow2B qB

/-- Pointwise check of the biased floor-logs against the verified fast
    forms over the whole biased-q domain, plus `-324 ≤ k` (so the bias
    never truncates). -/
def kBOfMQ_checkBool : Bool :=
  (List.range 2046).all fun qn =>
    decide (-324 ≤ floorLog10Pow2_fast ((qn : Int) - 1074))
    && decide ((floorLog10Pow2B (UInt64.ofNat qn)).toNat
        = (floorLog10Pow2_fast ((qn : Int) - 1074) + 324).toNat)
    && decide (-324 ≤ floorLog10ThreeQuartersPow2_fast ((qn : Int) - 1074))
    && decide ((floorLog10ThreeQuartersPow2B (UInt64.ofNat qn)).toNat
        = (floorLog10ThreeQuartersPow2_fast ((qn : Int) - 1074) + 324).toNat)

theorem kBOfMQ_check : kBOfMQ_checkBool = true := by decide +kernel

private theorem kB_facts (qn : Nat) (hq : qn < 2046) :
    (-324 ≤ floorLog10Pow2_fast ((qn : Int) - 1074)
      ∧ (floorLog10Pow2B (UInt64.ofNat qn)).toNat
          = (floorLog10Pow2_fast ((qn : Int) - 1074) + 324).toNat)
    ∧ (-324 ≤ floorLog10ThreeQuartersPow2_fast ((qn : Int) - 1074)
      ∧ (floorLog10ThreeQuartersPow2B (UInt64.ofNat qn)).toNat
          = (floorLog10ThreeQuartersPow2_fast ((qn : Int) - 1074) + 324).toNat) := by
  have hAll := kBOfMQ_check
  unfold kBOfMQ_checkBool at hAll
  rw [List.all_eq_true] at hAll
  have h := hAll qn (List.mem_range.mpr hq)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1.1, h.1.1.2⟩, ⟨h.1.2, h.2⟩⟩

theorem isIrregularB_eq (mU qB : UInt64) :
    isIrregularB mU qB = isIrregular mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold isIrregularB isIrregular minNormalSignificand minBinaryExp
  congr 1
  · refine decide_eq_decide.mpr ?_
    rw [← UInt64.toNat_inj, show ((4503599627370496 : UInt64)).toNat = 1 <<< 52 from rfl]
  · refine decide_eq_decide.mpr ?_
    rw [ge_iff_le, UInt64.le_iff_toNat_le, show ((1 : UInt64)).toNat = 1 from rfl]
    omega

theorem kBOfMQ_eq (mU qB : UInt64) (hq : qB.toNat ≤ 2045) :
    -324 ≤ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)
    ∧ (kBOfMQ mU qB).toNat
        = (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat := by
  have hf := kB_facts qB.toNat (by omega)
  rw [UInt64.ofNat_toNat] at hf
  unfold kBOfMQ kOfMQ_fast
  rw [isIrregularB_eq]
  by_cases hi : isIrregular mU.toNat ((qB.toNat : Int) - 1074) = true
  · simp only [hi, if_true]
    exact ⟨hf.2.1, hf.2.2⟩
  · simp only [Bool.not_eq_true] at hi
    simp only [hi, Bool.false_eq_true, if_false]
    exact ⟨hf.1.1, hf.1.2⟩

@[inline]
def shortestUnsigned_u64_opt_v8 (mU : UInt64) (qB : UInt64) : Option (UInt64 × Int) :=
  if _h_m0 : mU = 0 then none
  else if _h_m : mU ≥ (9007199254740992 : UInt64) then none
  else if _h_q : qB > 2045 then none
  else
    let irregular := isIrregularB mU qB
    let kB : UInt64 := kBOfMQ mU qB
    if _h_k : kB > 647 then none
    else
      let kBn : Nat := kB.toNat
      let k : Int := (kBn : Int) - 324
      let sigTuple := pow10Table192.getD (648 - kBn) pow10Table192_default
      let tA : UInt64 := (hB192.getD (648 - kBn) 0 + 4096) - qB
      let s : Nat :=
        if _h_s_lo : tA < 5258 then
          shiftedSig mU.toNat ((qB.toNat : Int) - 1074) k
        else if _h_s_hi : tA ≥ 5326 then
          shiftedSig mU.toNat ((qB.toNat : Int) - 1074) k
        else
          (shiftedSig_u192_kernel mU sigTuple.1 sigTuple.2.1
            sigTuple.2.2.1 (tA - 5070)).toNat
      if _h_s : s ≥ (1 <<< 57 : Nat) then none
      else
        let sU : UInt64 := UInt64.ofNat s
        if sU ≥ (10 : UInt64) then
          let cmpTupleH := pow10Table128.getD (kBn + 1) pow10Table128_default
          let uB : UInt64 := qB + hB128.getD (kBn + 1) 0
          if _h_qh_lo : uB < 3186 then none
          else if _h_qh_hi : uB > 3254 then none
          else
            let cmpHQPlusH8 : UInt64 := uB - 3122
            let sHighU : UInt64 := sU / 10
            let uV := inRoundingInterval_u64_packed_u8 cmpTupleH.1 cmpTupleH.2.1
                        cmpHQPlusH8 sHighU mU irregular
            if uV = inRoundingInterval_u8_AMBIG then none
            else if uV = inRoundingInterval_u8_TRUE then some (sHighU, k + 1)
            else
              let wV := inRoundingInterval_u64_packed_u8 cmpTupleH.1 cmpTupleH.2.1
                          cmpHQPlusH8 (sHighU + 1) mU irregular
              if wV = inRoundingInterval_u8_AMBIG then none
              else if wV = inRoundingInterval_u8_TRUE then some (sHighU + 1, k + 1)
              else
                let cmpTuple := pow10Table128.getD kBn pow10Table128_default
                let uC : UInt64 := qB + hB128.getD kBn 0
                if _h_qh2_lo : uC < 3186 then none
                else if _h_qh2_hi : uC > 3254 then none
                else
                  let cmpQPlusH8 : UInt64 := uC - 3122
                  match pickNearer_u64_opt cmpTuple.1 cmpTuple.2.1 cmpQPlusH8 sU mU irregular with
                  | none => none
                  | some chosen => some (chosen, k)
        else if _h_s1 : sU = 0 then none
        else
          let cmpTuple := pow10Table128.getD kBn pow10Table128_default
          let uC : UInt64 := qB + hB128.getD kBn 0
          if _h_qh2_lo : uC < 3186 then none
          else if _h_qh2_hi : uC > 3254 then none
          else
            let cmpQPlusH8 : UInt64 := uC - 3122
            match pickNearer_u64_opt cmpTuple.1 cmpTuple.2.1 cmpQPlusH8 sU mU irregular with
            | none => none
            | some chosen => some (chosen, k)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem shortestUnsigned_u64_opt_v8_eq_v7 (mU qB : UInt64) :
    shortestUnsigned_u64_opt_v8 mU qB
      = shortestUnsigned_u64_opt_v7 mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold shortestUnsigned_u64_opt_v8 shortestUnsigned_u64_opt_v7
  by_cases h_m0 : mU.toNat = 0
  · rw [dif_pos (UInt64.toNat_inj.mp h_m0), dif_pos h_m0]
  rw [dif_neg (fun hc => h_m0 (by rw [hc]; rfl)), dif_neg h_m0]
  by_cases h_m : mU.toNat ≥ 1 <<< 53
  · rw [dif_pos (by
        rw [ge_iff_le, UInt64.le_iff_toNat_le,
          show ((9007199254740992 : UInt64)).toNat = 1 <<< 53 from rfl]
        exact h_m),
      dif_pos h_m]
  rw [dif_neg (by
        rw [ge_iff_le, UInt64.le_iff_toNat_le,
          show ((9007199254740992 : UInt64)).toNat = 1 <<< 53 from rfl]
        exact h_m),
      dif_neg h_m]
  rw [dif_neg (show ¬ ((qB.toNat : Int) - 1074) < -1074 from by omega)]
  by_cases h_q : qB.toNat > 2045
  · rw [dif_pos (by
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((2045 : UInt64)).toNat = 2045 from rfl]
        exact h_q),
      dif_pos (show ((qB.toNat : Int) - 1074) > 971 from by omega)]
  rw [dif_neg (by
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((2045 : UInt64)).toNat = 2045 from rfl]
        exact h_q),
      dif_neg (show ¬ ((qB.toNat : Int) - 1074) > 971 from by omega)]
  have hkf := kBOfMQ_eq mU qB (by omega)
  have hknn := hkf.1
  have hkval := hkf.2
  have hkB : (kBOfMQ mU qB).toNat
      = (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat := hkval
  rw [dif_neg (show ¬ kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074)
        < pow10Table128_kMin from by
      have : pow10Table128_kMin = -324 := rfl
      omega)]
  by_cases h_k : kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 1 > pow10Table128_kMax
  · rw [dif_pos (by
        have hkm : pow10Table128_kMax = 324 := rfl
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((647 : UInt64)).toNat = 647 from rfl, hkB]
        omega),
      dif_pos h_k]
  rw [dif_neg (by
        have hkm : pow10Table128_kMax = 324 := rfl
        rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, show ((647 : UInt64)).toNat = 647 from rfl, hkB]
        omega),
      dif_neg h_k]
  -- align the body
  have ekexit : (((kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat : Int)) - 324
      = kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) := by
    omega
  have ekidx : (kBOfMQ mU qB).toNat
      = (kOfMQ_fast mU.toNat ((qB.toNat : Int) - 1074) + 324).toNat := hkB
  have eqb : UInt64.ofNat (((qB.toNat : Int) - 1074) + 1074).toNat = qB := by
    rw [show (((qB.toNat : Int) - 1074) + 1074).toNat = qB.toNat from by omega,
        UInt64.ofNat_toNat]
  have em : UInt64.ofNat mU.toNat = mU := UInt64.ofNat_toNat
  have eirr : isIrregular mU.toNat ((qB.toNat : Int) - 1074) = isIrregularB mU qB :=
    (isIrregularB_eq mU qB).symm
  simp only [ekidx, ekexit, eqb, em, eirr]

@[inline]
def shortestUnsigned_v8 (mU qB : UInt64) : Nat × Int :=
  match shortestUnsigned_u64_opt_v8 mU qB with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed mU.toNat ((qB.toNat : Int) - 1074)

theorem shortestUnsigned_v8_eq_v7 (mU qB : UInt64) :
    shortestUnsigned_v8 mU qB
      = shortestUnsigned_v7 mU.toNat ((qB.toNat : Int) - 1074) := by
  unfold shortestUnsigned_v8 shortestUnsigned_v7
  rw [shortestUnsigned_u64_opt_v8_eq_v7]

end PP.Numeric.Schubfach
