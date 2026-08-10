/- Performance variants `cmpScaledMixed_fast2` and `shiftedSig_fast2`:
   the fast UInt64 multiply-shift kernels plus the `@[csimp]` registrations
   that swap them in for the reference `cmpScaledMixed` / `shiftedSig` at
   compile time.

   The correctness theory (`shiftedSig_sandwich`, `shiftedSig_floor_safe`,
   `verdict_plus_one_correct`, `cmpScaledMixed_of_nonneg`, table-precision
   bounds, etc.) lives in `KernelCorrectness.lean` and is shared with the
   192-bit Perf variants in `Perf/Kernel192Correctness.lean`.  This file
   contains only the fast2-specific assembly:

   - `cmpScaledMixed_verdict_plus_one` / `_minus_one` — Int verdict bridges
   - `kernel_L_mid_zero` / `_mid_nonzero` / `_hi_zero` / `_hi_nonzero`
     — UInt64 shift kernel bridges for the L triple
   - `cmpScaledMixed_fast2_guards` — guard-fallback collapse
   - `cmpScaledMixed_strict_plus` / `_minus` — strict-verdict assemblies
   - `a_toNat_lt_60`, `qPlusH_toNat_in_range` — narrow bound helpers
   - `cmpScaledMixed_eq_fast2`, `shiftedSig_eq_fast2` — final equalities
   - `shiftedSig_fast2_guards` — guard-fallback for shiftedSig
   - `@[csimp]` registrations swapping the references for the fast2 forms

   The two `@[csimp]` registrations at the bottom drive the bench-side
   speedup: at runtime the compiler will call the UInt64 multiply-shift
   kernels everywhere the reference `cmpScaledMixed` / `shiftedSig` appears,
   while definitional equality with the reference is preserved by the
   proofs in this file. -/
import Srtfp.Schubfach
import Srtfp.Tactics
import Srtfp.Schubfach.Kernel192
import Srtfp.Schubfach.KernelCorrectness
import Srtfp.Schubfach.TableInvariant

namespace Srtfp.Schubfach

set_option maxHeartbeats 1000000

/-! ## Strict-verdict assembly

These lemmas put the pieces together: given the kernel hypotheses
(a ≥ 0, b > 0, a < 2^60, k in table range, q+h ∈ [64, 192)), assemble
the Nat verdicts into Int verdicts on `cmpScaledMixed`.

The cleanest formulation is to expose the strict-verdict
conclusions in terms of `L = a · 2^(q+h)` and `R = b · g` (Nat). -/

/-- Bridge: if the strict `+1` verdict `L > R` holds for `L = a · 2^s`,
    `R = b · g`, and the table invariant holds, then
    `cmpScaledMixed a q b k = 1`.

    Hypotheses are written for direct discharging from the kernel:
    `a ≥ 0`, `b > 0`, `s = q + h` (Int), `k ∈ [kMin, kMax]`. -/
theorem cmpScaledMixed_verdict_plus_one
    (a b q k h : Int)
    (ha : 0 ≤ a) (hb_pos : 0 < b)
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (hh_eq : h = (pow10Lookup128 k).2.2)
    (hVerdict : a.toNat * 2 ^ (q + h).toNat
                  > b.toNat * ((pow10Lookup128 k).1.toNat * 2 ^ 64
                                + (pow10Lookup128 k).2.1.toNat))
    (hqh_nonneg : 0 ≤ q + h) :
    cmpScaledMixed a q b k = 1 := by
  -- Step 1: extract `(gHi, gLo)` and `g = gHi · 2^64 + gLo`.
  set gHi := (pow10Lookup128 k).1
  set gLo := (pow10Lookup128 k).2.1
  set g : Nat := gHi.toNat * 2 ^ 64 + gLo.toNat
  -- Use the table invariant.
  have hInv := pow10Lookup128_invariant k hk_lo hk_hi
  simp only [← hh_eq] at hInv
  set kPos : Nat := if k ≥ 0 then k.toNat else 0 with hkPos_def
  set kNeg : Nat := if k < 0 then (-k).toNat else 0 with hkNeg_def
  set hPos : Nat := if h ≥ 0 then h.toNat else 0 with hhPos_def
  set hNeg : Nat := if h < 0 then (-h).toNat else 0 with hhNeg_def
  -- Pull out the invariant components.
  have hInv_eq : 10 ^ kPos * 2 ^ hPos ≤ g * 10 ^ kNeg * 2 ^ hNeg
                  ∧ g * 10 ^ kNeg * 2 ^ hNeg < 10 ^ kPos * 2 ^ hPos + 10 ^ kNeg * 2 ^ hNeg := hInv
  -- Step 2: apply verdict_plus_one_correct (Nat verdict).
  -- s := q + h is the shift amount (≥ 0).
  set s : Nat := (q + h).toNat with hs_def
  have hVerdict_nat : a.toNat * 2 ^ s > b.toNat * g := hVerdict
  have hb_pos_nat : 0 < b.toNat := by
    have h : (0 : Int) < b := hb_pos
    omega
  have hVPlus := verdict_plus_one_correct a.toNat g b.toNat kPos kNeg hPos hNeg s
                    hb_pos_nat hInv_eq hVerdict_nat
  -- hVPlus : a.toNat · 2^s · 10^kNeg · 2^hNeg > b.toNat · (10^kPos · 2^hPos)
  -- Step 3: convert s = q + h via regrouping.
  -- We use Int equation: (q + h) = q + h, then split each into pos/neg parts.
  have hSplit := two_pow_regroup_of_eq q h (q + h) rfl
  -- hSplit : sPos + qNeg + hNeg = qPos + hPos + sNeg
  -- Where sPos = s.toNat (since q+h ≥ 0).
  set qPos : Nat := if q ≥ 0 then q.toNat else 0 with hqPos_def
  set qNeg : Nat := if q < 0 then (-q).toNat else 0 with hqNeg_def
  have hsPos_eq : (if q + h ≥ 0 then (q + h).toNat else 0) = s := by
    rw [hs_def]
    by_cases h0 : q + h ≥ 0
    · simp [h0]
    · simp [h0]; omega
  have hsNeg_zero : (if q + h < 0 then (-(q + h)).toNat else 0) = 0 := by
    by_cases h0 : q + h < 0
    · omega
    · simp [h0]
  -- Unfold hSplit's let-bindings before rewriting.
  have hSplit' : (if q + h ≥ 0 then (q + h).toNat else 0) + qNeg + hNeg =
                  qPos + hPos + (if q + h < 0 then (-(q + h)).toNat else 0) := hSplit
  rw [hsPos_eq, hsNeg_zero, Nat.add_zero] at hSplit'
  -- hSplit' : s + qNeg + hNeg = qPos + hPos
  -- Step 4: regroup powers via two_pow_regroup.
  have hRegroup : 2 ^ s * 2 ^ qNeg * 2 ^ hNeg = 2 ^ qPos * 2 ^ hPos :=
    two_pow_regroup s qPos qNeg hPos hNeg hSplit'
  -- Step 5: apply cmpScaledMixed_plus_one to translate verdict to Nat comparison.
  have hNat := cmpScaledMixed_plus_one a.toNat b.toNat s qPos qNeg hPos hNeg kPos kNeg hRegroup hVPlus
  -- hNat : a.toNat · 2^qPos · 10^kNeg > b.toNat · 10^kPos · 2^qNeg
  -- Step 6: reduce cmpScaledMixed to Nat form and conclude.
  have hb_nonneg : 0 ≤ b := Int.le_of_lt hb_pos
  have hReduce := cmpScaledMixed_of_nonneg a b q k ha hb_nonneg
  rw [hReduce]
  -- Now goal: if lhsN < rhsN then -1 else if lhsN = rhsN then 0 else 1 = 1
  -- We have lhsN > rhsN, so the result is 1.
  have hnLt : ¬ a.toNat * 2 ^ qPos * 10 ^ kNeg < b.toNat * 10 ^ kPos * 2 ^ qNeg := by omega
  have hnEq : ¬ a.toNat * 2 ^ qPos * 10 ^ kNeg = b.toNat * 10 ^ kPos * 2 ^ qNeg := by omega
  rw [if_neg hnLt, if_neg hnEq]

/-- Bridge: if the strict `-1` verdict `L + b ≤ R` holds for `L = a · 2^s`,
    `R = b · g`, then `cmpScaledMixed a q b k = -1`. -/
theorem cmpScaledMixed_verdict_minus_one
    (a b q k h : Int)
    (ha : 0 ≤ a) (hb_pos : 0 < b)
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (hh_eq : h = (pow10Lookup128 k).2.2)
    (hVerdict : a.toNat * 2 ^ (q + h).toNat + b.toNat
                  ≤ b.toNat * ((pow10Lookup128 k).1.toNat * 2 ^ 64
                                + (pow10Lookup128 k).2.1.toNat))
    (hqh_nonneg : 0 ≤ q + h) :
    cmpScaledMixed a q b k = -1 := by
  set gHi := (pow10Lookup128 k).1
  set gLo := (pow10Lookup128 k).2.1
  set g : Nat := gHi.toNat * 2 ^ 64 + gLo.toNat
  have hInv := pow10Lookup128_invariant k hk_lo hk_hi
  simp only [← hh_eq] at hInv
  set kPos : Nat := if k ≥ 0 then k.toNat else 0 with hkPos_def
  set kNeg : Nat := if k < 0 then (-k).toNat else 0 with hkNeg_def
  set hPos : Nat := if h ≥ 0 then h.toNat else 0 with hhPos_def
  set hNeg : Nat := if h < 0 then (-h).toNat else 0 with hhNeg_def
  have hInv_eq : 10 ^ kPos * 2 ^ hPos ≤ g * 10 ^ kNeg * 2 ^ hNeg
                  ∧ g * 10 ^ kNeg * 2 ^ hNeg < 10 ^ kPos * 2 ^ hPos + 10 ^ kNeg * 2 ^ hNeg := hInv
  set s : Nat := (q + h).toNat with hs_def
  have hb_pos_nat : 0 < b.toNat := by
    have h : (0 : Int) < b := hb_pos
    omega
  have hVerdict_nat : a.toNat * 2 ^ s + b.toNat ≤ b.toNat * g := hVerdict
  have hVMinus := verdict_minus_one_correct a.toNat g b.toNat kPos kNeg hPos hNeg s
                    hb_pos_nat hInv_eq hVerdict_nat
  -- hVMinus : a.toNat · 2^s · 10^kNeg · 2^hNeg < b.toNat · (10^kPos · 2^hPos)
  have hSplit := two_pow_regroup_of_eq q h (q + h) rfl
  set qPos : Nat := if q ≥ 0 then q.toNat else 0 with hqPos_def
  set qNeg : Nat := if q < 0 then (-q).toNat else 0 with hqNeg_def
  have hsPos_eq : (if q + h ≥ 0 then (q + h).toNat else 0) = s := by
    rw [hs_def]
    by_cases h0 : q + h ≥ 0
    · simp [h0]
    · simp [h0]; omega
  have hsNeg_zero : (if q + h < 0 then (-(q + h)).toNat else 0) = 0 := by
    by_cases h0 : q + h < 0
    · omega
    · simp [h0]
  have hSplit' : (if q + h ≥ 0 then (q + h).toNat else 0) + qNeg + hNeg =
                  qPos + hPos + (if q + h < 0 then (-(q + h)).toNat else 0) := hSplit
  rw [hsPos_eq, hsNeg_zero, Nat.add_zero] at hSplit'
  have hRegroup : 2 ^ s * 2 ^ qNeg * 2 ^ hNeg = 2 ^ qPos * 2 ^ hPos :=
    two_pow_regroup s qPos qNeg hPos hNeg hSplit'
  have hNat := cmpScaledMixed_minus_one a.toNat b.toNat s qPos qNeg hPos hNeg kPos kNeg hRegroup hVMinus
  -- hNat : a.toNat · 2^qPos · 10^kNeg < b.toNat · 10^kPos · 2^qNeg
  have hb_nonneg : 0 ≤ b := Int.le_of_lt hb_pos
  have hReduce := cmpScaledMixed_of_nonneg a b q k ha hb_nonneg
  rw [hReduce]
  have hLt : a.toNat * 2 ^ qPos * 10 ^ kNeg < b.toNat * 10 ^ kPos * 2 ^ qNeg := hNat
  rw [if_pos hLt]

/-! ## Final assembly: `cmpScaledMixed_eq_fast2`

The main theorem that closes the axiom.  Strategy:

1. Unfold `cmpScaledMixed_fast2`.
2. For each guard-fallback branch, reduce to `cmpScaledMixed_fast`
   via `cmpScaledMixed_eq_fast`.
3. In the strict-verdict branches:
   - Extract `aU.toNat = a.toNat`, `bU.toNat = b.toNat`.
   - Compute `R.toNat` via `kernel_R_eq` (exact since `b < 2^60`).
   - Compute `L.toNat` via `shift_kernel_*_eq` (cases on `s < 128`).
   - Apply `cmpScaledMixed_verdict_plus_one` / `_minus_one`.
4. For the ambiguous fallback (neither `gt192` nor `le192` fires),
   reduce to `cmpScaledMixed_fast` via `cmpScaledMixed_eq_fast`. -/

/-- Mid-branch shift-kernel correctness, threading
    `shift_kernel_mid_eq` through the UInt64 dispatch.

    When `s.toNat ∈ [64, 128)` and `aU.toNat < 2^60`, the triple
    `(aU >>> (64 - s64), aU <<< s64, 0)` (or `(0, aU, 0)` for `s64 = 0`)
    equals `aU.toNat * 2^s.toNat`.  Split into the two `s64`-cases for
    direct discharge from the kernel. -/
theorem kernel_L_mid_zero (aU : UInt64) (s : UInt64) (s64 : UInt64)
    (_haU_lt : aU.toNat < 2 ^ 60)
    (hs_toNat_lo : 64 ≤ s.toNat) (hs_toNat_hi : s.toNat < 128)
    (hs64_def : s64 = s - 64) (hs64_zero : s64 = 0) (qpn : Nat) (hqpn : qpn = s.toNat) :
    triple192Nat 0 aU 0 = aU.toNat * 2 ^ qpn := by
  have hs64_toNat : s64.toNat = s.toNat - 64 := by
    rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 64 (by decide) hs_toNat_lo
  have hs64_toNat0 : s64.toNat = 0 := by rw [hs64_zero]; rfl
  -- s.toNat - 64 = 0 ⇒ s.toNat = 64 ⇒ qpn = 64.
  have hqpn_eq : qpn = 64 := by omega
  rw [hqpn_eq]
  -- Goal: triple192Nat 0 aU 0 = aU.toNat * 2^64
  unfold triple192Nat
  simp [UInt64.toNat_ofNat]

theorem kernel_L_mid_nonzero (aU : UInt64) (s : UInt64) (s64 : UInt64)
    (haU_lt : aU.toNat < 2 ^ 60)
    (hs_toNat_lo : 64 ≤ s.toNat) (hs_toNat_hi : s.toNat < 128)
    (hs64_def : s64 = s - 64) (hs64_nz : s64 ≠ 0) (qpn : Nat) (hqpn : qpn = s.toNat) :
    triple192Nat (aU >>> (UInt64.ofNat (64 - s64.toNat))) (aU <<< s64) 0
      = aU.toNat * 2 ^ qpn := by
  have hs64_toNat : s64.toNat = s.toNat - 64 := by
    rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 64 (by decide) hs_toNat_lo
  have hs64_lt_64 : s64.toNat < 64 := by omega
  have hs64_pos : 0 < s64.toNat := by
    have : s64.toNat ≠ 0 := fun h => hs64_nz (UInt64.toNat_inj.mp (h.trans (by decide)))
    omega
  have hs64_inj : UInt64.ofNat s64.toNat = s64 := by
    have hbd : s64.toNat < 2 ^ 64 := by
      have h264 : (64 : Nat) < 2 ^ 64 := by decide
      omega
    rw [← UInt64.toNat_inj, UInt64_ofNat_toNat_of_lt _ hbd]
  -- Use shift_kernel_mid_eq with the nonzero branch.
  have hmid := shift_kernel_mid_eq aU s64.toNat hs64_lt_64
  simp only at hmid
  -- The if condition `s64.toNat = 0` is false (hs64_pos).
  have hne : s64.toNat ≠ 0 := by omega
  rw [if_neg hne] at hmid
  -- Replace UInt64.ofNat s64.toNat → s64 only in the shift-left position.
  -- (The shift-right uses UInt64.ofNat (64 - s64.toNat), which matches our goal.)
  -- hmid : triple192Nat (aU >>> UInt64.ofNat (64-s64.toNat)) (aU <<< UInt64.ofNat s64.toNat) 0
  --        = (aU.toNat * 2^(s64.toNat+64)) % 2^192
  conv at hmid => rw [show UInt64.ofNat s64.toNat = s64 from hs64_inj]
  have hsum_eq : s64.toNat + 64 = qpn := by omega
  rw [hsum_eq] at hmid
  have hprod_lt : aU.toNat * 2 ^ qpn < 2 ^ 192 := by
    have hqpn_le : qpn ≤ 132 := by omega
    have h2qpn_le : (2 : Nat) ^ qpn ≤ 2 ^ 132 := Nat.pow_le_pow_right (by decide) hqpn_le
    have h1 : aU.toNat * 2 ^ qpn ≤ aU.toNat * 2 ^ 132 := Nat.mul_le_mul_left _ h2qpn_le
    have h60_132 : aU.toNat * 2 ^ 132 < 2 ^ 60 * 2 ^ 132 :=
      Nat.mul_lt_mul_of_pos_right haU_lt (Nat.two_pow_pos _)
    have h_192 : (2 : Nat) ^ 60 * 2 ^ 132 = 2 ^ 192 := by rw [← Nat.pow_add]
    omega
  rw [Nat.mod_eq_of_lt hprod_lt] at hmid
  exact hmid

theorem kernel_L_hi_zero (aU : UInt64) (s : UInt64) (s64 : UInt64)
    (_haU_lt : aU.toNat < 2 ^ 60)
    (hs_toNat_lo : 128 ≤ s.toNat) (hs_toNat_hi : s.toNat ≤ 132)
    (hs64_def : s64 = s - 128) (hs64_zero : s64 = 0) (qpn : Nat) (hqpn : qpn = s.toNat) :
    triple192Nat aU 0 0 = aU.toNat * 2 ^ qpn := by
  have hs64_toNat : s64.toNat = s.toNat - 128 := by
    rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 128 (by decide) hs_toNat_lo
  have hs64_toNat0 : s64.toNat = 0 := by rw [hs64_zero]; rfl
  have hqpn_eq : qpn = 128 := by omega
  rw [hqpn_eq]
  unfold triple192Nat
  simp [UInt64.toNat_ofNat]

theorem kernel_L_hi_nonzero (aU : UInt64) (s : UInt64) (s64 : UInt64)
    (haU_lt : aU.toNat < 2 ^ 60)
    (hs_toNat_lo : 128 ≤ s.toNat) (hs_toNat_hi : s.toNat ≤ 132)
    (hs64_def : s64 = s - 128) (hs64_nz : s64 ≠ 0) (qpn : Nat) (hqpn : qpn = s.toNat) :
    triple192Nat (aU <<< s64) 0 0 = aU.toNat * 2 ^ qpn := by
  have hs64_toNat : s64.toNat = s.toNat - 128 := by
    rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 128 (by decide) hs_toNat_lo
  have hs64_lt_64 : s64.toNat < 64 := by omega
  have hs64_le_4 : s64.toNat ≤ 4 := by omega
  have hs64_pos : 0 < s64.toNat := by
    have : s64.toNat ≠ 0 := fun h => hs64_nz (UInt64.toNat_inj.mp (h.trans (by decide)))
    omega
  have ha_lt_64ms64 : aU.toNat < 2 ^ (64 - s64.toNat) := by
    have h64s : 60 ≤ 64 - s64.toNat := by omega
    have : (2 : Nat) ^ 60 ≤ 2 ^ (64 - s64.toNat) := Nat.pow_le_pow_right (by decide) h64s
    omega
  have hs64_inj : UInt64.ofNat s64.toNat = s64 := by
    have hbd : s64.toNat < 2 ^ 64 := by
      have h264 : (64 : Nat) < 2 ^ 64 := by decide
      omega
    rw [← UInt64.toNat_inj, UInt64_ofNat_toNat_of_lt _ hbd]
  have hhi := shift_kernel_hi_eq aU s64.toNat hs64_lt_64 ha_lt_64ms64
  simp only at hhi
  have hne : s64.toNat ≠ 0 := by omega
  rw [if_neg hne] at hhi
  conv at hhi => rw [show UInt64.ofNat s64.toNat = s64 from hs64_inj]
  have hsum_eq : s64.toNat + 128 = qpn := by omega
  rw [hsum_eq] at hhi
  exact hhi

/-! ## Easy guard-fallback branches of `cmpScaledMixed_eq_fast2`

This section closes the case-tree of `cmpScaledMixed_fast2` for all
guard branches that fall back to `cmpScaledMixed_fast`.  The
strict-verdict branches require the full Phase-4/6 case analysis
(left as future work — see `cmpScaledMixed_eq_fast2` in `Schubfach.lean`). -/

/-- Reduce `cmpScaledMixed_fast2 a q b k` to `cmpScaledMixed_fast a q b k`
    when the kernel's early guards fire (any of: `a < 0`, `b < 0`, `b = 0`,
    `a ≥ 2^60`, `b ≥ 2^60`, `k` out of table range).  -/
theorem cmpScaledMixed_fast2_guards
    (a : Int) (q : Int) (b : Int) (k : Int)
    (hGuard : a < 0 ∨ b < 0 ∨ b = 0 ∨ a ≥ (1 <<< 60 : Int) ∨ b ≥ (1 <<< 60 : Int)
              ∨ k < pow10Table128_kMin ∨ k > pow10Table128_kMax) :
    cmpScaledMixed_fast2 a q b k = cmpScaledMixed_fast a q b k := by
  unfold cmpScaledMixed_fast2
  rcases hGuard with h | h | h | h | h | h | h
  · simp only [if_pos (Or.inl h)]
  · simp only [if_pos (Or.inr h)]
  · by_cases h1 : a < 0 ∨ b < 0
    · simp only [if_pos h1]
    · simp only [if_neg h1, if_pos h]
  · by_cases h1 : a < 0 ∨ b < 0
    · simp only [if_pos h1]
    · by_cases h2 : b = 0
      · simp only [if_neg h1, if_pos h2]
      · simp only [if_neg h1, if_neg h2, if_pos (Or.inl h)]
  · by_cases h1 : a < 0 ∨ b < 0
    · simp only [if_pos h1]
    · by_cases h2 : b = 0
      · simp only [if_neg h1, if_pos h2]
      · simp only [if_neg h1, if_neg h2, if_pos (Or.inr h)]
  · by_cases h1 : a < 0 ∨ b < 0
    · simp only [if_pos h1]
    · by_cases h2 : b = 0
      · simp only [if_neg h1, if_pos h2]
      · by_cases h3 : a ≥ (1 <<< 60 : Int) ∨ b ≥ (1 <<< 60 : Int)
        · simp only [if_neg h1, if_neg h2, if_pos h3]
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos (Or.inl h)]
  · by_cases h1 : a < 0 ∨ b < 0
    · simp only [if_pos h1]
    · by_cases h2 : b = 0
      · simp only [if_neg h1, if_pos h2]
      · by_cases h3 : a ≥ (1 <<< 60 : Int) ∨ b ≥ (1 <<< 60 : Int)
        · simp only [if_neg h1, if_neg h2, if_pos h3]
        · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos (Or.inr h)]

/-! ## Strict-verdict +1 / -1 with pre-extracted kernel values

These two lemmas assume the kernel has already computed its `L` and
`R` triples (as explicit UInt64s), then concludes the +1 or -1
verdict.  The main theorem will reduce to these after the kernel's
`let`s are unfolded. -/

/-- Strict +1 branch.  Assumes the caller has computed `L = a · 2^(q+h)`
    and `R = b · g` (as triples) such that `L.toNat > R.toNat`, and the
    table invariant holds with the given `(kPos, kNeg, hPos, hNeg)`.
    Concludes `cmpScaledMixed a q b k = 1`. -/
theorem cmpScaledMixed_strict_plus
    (a q b k : Int)
    (l_hi l_mid l_lo : UInt64) (r_hi r_mid r_lo : UInt64)
    (ha_nn : 0 ≤ a) (hb_pos : 0 < b)
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (h : Int) (hh_eq : h = (pow10Lookup128 k).2.2)
    (hL_toNat : triple192Nat l_hi l_mid l_lo = a.toNat * 2 ^ (q + h).toNat)
    (hR_toNat : triple192Nat r_hi r_mid r_lo
                  = b.toNat * ((pow10Lookup128 k).1.toNat * 2 ^ 64
                                + (pow10Lookup128 k).2.1.toNat))
    (hqh_nonneg : 0 ≤ q + h)
    (hGt : gt192 l_hi l_mid l_lo r_hi r_mid r_lo = true) :
    cmpScaledMixed a q b k = 1 := by
  -- gt192 ⇒ L.toNat > R.toNat (Nat order).
  have hgt_nat : triple192Nat l_hi l_mid l_lo > triple192Nat r_hi r_mid r_lo :=
    (gt192_iff l_hi l_mid l_lo r_hi r_mid r_lo).mp hGt
  rw [hL_toNat, hR_toNat] at hgt_nat
  -- Verdict bridge.
  exact cmpScaledMixed_verdict_plus_one a b q k h ha_nn hb_pos hk_lo hk_hi hh_eq hgt_nat hqh_nonneg

/-- Strict -1 branch.  Assumes the caller has computed `L`, `R`, and
    `L + b ≤ R`.  Concludes `cmpScaledMixed a q b k = -1`. -/
theorem cmpScaledMixed_strict_minus
    (a q b k : Int)
    (l_hi l_mid l_lo : UInt64) (r_hi r_mid r_lo : UInt64) (bU : UInt64)
    (ha_nn : 0 ≤ a) (hb_pos : 0 < b) (hb_lt : b < (1 <<< 60 : Int))
    (hbU_eq : bU.toNat = b.toNat)
    (hk_lo : pow10Table128_kMin ≤ k) (hk_hi : k ≤ pow10Table128_kMax)
    (h : Int) (hh_eq : h = (pow10Lookup128 k).2.2)
    (hL_toNat : triple192Nat l_hi l_mid l_lo = a.toNat * 2 ^ (q + h).toNat)
    (hR_toNat : triple192Nat r_hi r_mid r_lo
                  = b.toNat * ((pow10Lookup128 k).1.toNat * 2 ^ 64
                                + (pow10Lookup128 k).2.1.toNat))
    (hqh_nonneg : 0 ≤ q + h)
    (hNotGt : gt192 l_hi l_mid l_lo r_hi r_mid r_lo = false)
    (hLe : le192 (add192_64 l_hi l_mid l_lo bU).1
                 (add192_64 l_hi l_mid l_lo bU).2.1
                 (add192_64 l_hi l_mid l_lo bU).2.2
                 r_hi r_mid r_lo = true) :
    cmpScaledMixed a q b k = -1 := by
  -- ¬ gt192 ⇒ L ≤ R.
  -- le192 (L + b) R ⇒ (L + b mod 2^192) ≤ R.
  -- We need to show L + b ≤ R (without mod).
  -- L ≤ R < 2^192, and b < 2^60, so L + b < 2^192 + 2^60 — but we need
  -- a tighter bound that L + b doesn't wrap.
  -- Key: L < 2^192 and b < 2^60, but the kernel computes L + b modulo
  -- 2^192.  We need L + b < 2^192, which follows from R < 2^192 (since
  -- L + b ≤ R via le192_iff).  Wait — le192_iff gives (L+b mod 2^192) ≤ R.
  -- We need L + b ≤ R without mod, which is the case iff L + b < 2^192.
  -- Since R < 2^192 and (L+b mod 2^192) ≤ R, if no wrap happens, OK.
  -- If wrap happens, (L+b mod 2^192) = L + b - 2^192, and the inequality
  -- gives L + b ≤ R + 2^192.  But this could be much larger than R.
  --
  -- Argument: from ¬gt192 we get L ≤ R.  Combined with L + b ≤ R + 2^192
  -- (modular wrap), and R < 2^192, b < 2^60, we'd have L + b ≤ R + 2^192,
  -- but we need L + b ≤ R.  This requires showing L + b doesn't wrap.
  --
  -- Bound: triple192Nat l ≤ triple192Nat r (from ¬gt192).
  -- triple192Nat r < 2^192.  L.toNat ≤ R.toNat < 2^192.
  -- b.toNat < 2^60.  So L.toNat + b.toNat < 2^192 + 2^60.  Not enough.
  -- But actually, given R = b · g < 2^60 · 2^128 = 2^188, we have R.toNat < 2^188.
  -- So L.toNat ≤ R.toNat < 2^188, hence L.toNat + b.toNat < 2^188 + 2^60 < 2^192.
  have hb_pos_nat : 0 < b.toNat := by omega
  have hb_toNat_lt : b.toNat < 2 ^ 60 := by
    have h60 : (1 <<< 60 : Int) = (2 : Int) ^ 60 := by decide
    rw [h60] at hb_lt
    have : (b.toNat : Int) < ((2 ^ 60 : Nat) : Int) := by
      rw [Int.toNat_of_nonneg (Int.le_of_lt hb_pos)]
      omega
    exact_mod_cast this
  -- R.toNat = b.toNat * g where g < 2^128.  So R.toNat < 2^60 · 2^128 = 2^188.
  have hgHi : (pow10Lookup128 k).1.toNat < 2 ^ 64 := (pow10Lookup128 k).1.toNat_lt
  have hgLo : (pow10Lookup128 k).2.1.toNat < 2 ^ 64 := (pow10Lookup128 k).2.1.toNat_lt
  have hg_lt : (pow10Lookup128 k).1.toNat * 2 ^ 64 + (pow10Lookup128 k).2.1.toNat < 2 ^ 128 := by
    have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
    have h1 : (pow10Lookup128 k).1.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
      apply Nat.mul_le_mul_right; omega
    have h2 : (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 64 * 2 ^ 64 := by
      have hpow_pos : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
      have : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
        rw [Nat.sub_mul]
      omega
    omega
  have hR_lt_188 : triple192Nat r_hi r_mid r_lo < 2 ^ 188 := by
    rw [hR_toNat]
    have : b.toNat * ((pow10Lookup128 k).1.toNat * 2 ^ 64 + (pow10Lookup128 k).2.1.toNat)
              < 2 ^ 60 * 2 ^ 128 :=
      Nat.mul_lt_mul_of_lt_of_lt hb_toNat_lt hg_lt
    have h188 : (2 : Nat) ^ 60 * 2 ^ 128 = 2 ^ 188 := by rw [← Nat.pow_add]
    omega
  -- L.toNat ≤ R.toNat (from ¬gt192).
  have hL_le_R : triple192Nat l_hi l_mid l_lo ≤ triple192Nat r_hi r_mid r_lo := by
    by_contra hContra
    push_neg at hContra
    have hgt_true : gt192 l_hi l_mid l_lo r_hi r_mid r_lo = true :=
      (gt192_iff l_hi l_mid l_lo r_hi r_mid r_lo).mpr hContra
    rw [hgt_true] at hNotGt
    exact absurd hNotGt (by decide)
  -- L.toNat + b.toNat < 2^188 + 2^60 < 2^192 (no wrap).
  have hsum_lt_192 : triple192Nat l_hi l_mid l_lo + b.toNat < 2 ^ 192 := by
    have h188_60 : (2 : Nat) ^ 188 + 2 ^ 60 < 2 ^ 192 := by decide
    omega
  -- add192_64_toNat: triple192Nat (add192_64 l bU) = (L.toNat + bU.toNat) mod 2^192.
  -- Since the sum is < 2^192, the mod is trivial.
  have hadd := add192_64_toNat l_hi l_mid l_lo bU
  simp only at hadd
  -- hadd : triple192Nat (...).1 (...).2.1 (...).2.2 = (L.toNat + bU.toNat) % 2^192
  rw [hbU_eq] at hadd
  rw [Nat.mod_eq_of_lt hsum_lt_192] at hadd
  -- le192 ⇒ Nat ≤.
  have hle_nat : triple192Nat (add192_64 l_hi l_mid l_lo bU).1
                              (add192_64 l_hi l_mid l_lo bU).2.1
                              (add192_64 l_hi l_mid l_lo bU).2.2
                  ≤ triple192Nat r_hi r_mid r_lo :=
    (le192_iff _ _ _ _ _ _).mp hLe
  rw [hadd, hL_toNat, hR_toNat] at hle_nat
  -- hle_nat : a.toNat * 2^(q+h).toNat + b.toNat ≤ b.toNat * g
  -- Verdict bridge.
  exact cmpScaledMixed_verdict_minus_one a b q k h ha_nn hb_pos hk_lo hk_hi hh_eq hle_nat hqh_nonneg

/-! ## Helper: bound `a.toNat` and `(q+h).toNat` from kernel preconditions -/

theorem a_toNat_lt_60 (a : Int) (ha_nn : 0 ≤ a) (ha_lt : a < (1 <<< 60 : Int)) :
    a.toNat < 2 ^ 60 := by
  have h60 : (1 <<< 60 : Int) = (2 : Int) ^ 60 := by decide
  rw [h60] at ha_lt
  have : (a.toNat : Int) < ((2 ^ 60 : Nat) : Int) := by
    rw [Int.toNat_of_nonneg ha_nn]
    omega
  exact_mod_cast this

theorem qPlusH_toNat_in_range (qPlusH : Int)
    (hqh_lo : ¬ (qPlusH < 64 ∨ 192 ≤ qPlusH)) (hqh_hi : ¬ 132 < qPlusH) :
    64 ≤ qPlusH.toNat ∧ qPlusH.toNat ≤ 132 := by
  push_neg at hqh_lo hqh_hi
  obtain ⟨h1, h2⟩ := hqh_lo
  have hnn : 0 ≤ qPlusH := by omega
  have heq : (qPlusH.toNat : Int) = qPlusH := Int.toNat_of_nonneg hnn
  refine ⟨?_, ?_⟩
  · have : (64 : Int) ≤ (qPlusH.toNat : Int) := heq.symm ▸ h1
    exact_mod_cast this
  · have : (qPlusH.toNat : Int) ≤ 132 := heq.symm ▸ hqh_hi
    exact_mod_cast this

/-! ## Final assembly: `cmpScaledMixed_eq_fast2` and `shiftedSig_eq_fast2` -/

set_option maxRecDepth 4000 in
theorem cmpScaledMixed_eq_fast2 (a : Int) (q : Int) (b : Int) (k : Int) :
    cmpScaledMixed a q b k = cmpScaledMixed_fast2 a q b k := by
  -- Strategy: case-split on the kernel guards.  All guard branches
  -- reduce to `cmpScaledMixed_fast` (via `cmpScaledMixed_fast2_guards`
  -- for the early guards, or via direct unfolding for the inner
  -- guards).  Only the strict-verdict branches need new work.
  -- Stage 1: early guards.
  by_cases hab : a < 0 ∨ b < 0
  · rw [cmpScaledMixed_eq_fast]
    rcases hab with h | h
    · exact (cmpScaledMixed_fast2_guards a q b k (Or.inl h)).symm
    · exact (cmpScaledMixed_fast2_guards a q b k (Or.inr (Or.inl h))).symm
  by_cases hb0 : b = 0
  · rw [cmpScaledMixed_eq_fast]
    exact (cmpScaledMixed_fast2_guards a q b k (Or.inr (Or.inr (Or.inl hb0)))).symm
  by_cases hab60 : a ≥ (1 <<< 60 : Int) ∨ b ≥ (1 <<< 60 : Int)
  · rw [cmpScaledMixed_eq_fast]
    rcases hab60 with h | h
    · exact (cmpScaledMixed_fast2_guards a q b k
              (Or.inr (Or.inr (Or.inr (Or.inl h))))).symm
    · exact (cmpScaledMixed_fast2_guards a q b k
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).symm
  by_cases hk : k < pow10Table128_kMin ∨ k > pow10Table128_kMax
  · rw [cmpScaledMixed_eq_fast]
    rcases hk with h | h
    · exact (cmpScaledMixed_fast2_guards a q b k
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).symm
    · exact (cmpScaledMixed_fast2_guards a q b k
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))).symm
  -- Stage 1 complete: we now have the kernel's inner positive precondition.
  push_neg at hab hab60 hk
  obtain ⟨ha_nn, hb_nn⟩ := hab
  obtain ⟨ha_lt, hb_lt⟩ := hab60
  obtain ⟨hk_lo, hk_hi⟩ := hk
  have hb_pos : 0 < b := by omega
  -- Open the kernel and discharge the resolved guards.
  rw [cmpScaledMixed_eq_fast]
  unfold cmpScaledMixed_fast2
  rw [if_neg (by push_neg; exact ⟨ha_nn, hb_nn⟩)]
  rw [if_neg hb0]
  rw [if_neg (by push_neg; exact ⟨ha_lt, hb_lt⟩)]
  rw [if_neg (by push_neg; exact ⟨hk_lo, hk_hi⟩)]
  -- Now bind the table lookup as opaque.
  set gTuple := pow10Lookup128 k with hgTuple
  -- Stage 2: inner guards on `q + h` (the destructuring is over `gTuple`).
  -- The kernel writes `let (gHi, gLo, h) := pow10Lookup128 k in ...`.
  -- After our `set`, the body becomes `match gTuple with | (gHi, gLo, h) => ...`.
  -- Rewrite using product eta + Prod.mk pattern.
  obtain ⟨gHi, gLo, h⟩ := gTuple
  -- Now we have explicit names.
  by_cases hqh_lo : q + h < 64 ∨ q + h ≥ 192
  · -- Inner low/high guard: falls back to `cmpScaledMixed_fast`.
    simp only [if_pos hqh_lo]
  -- Otherwise.
  simp only [if_neg hqh_lo]
  by_cases hqh_hi : q + h > 132
  · -- Upper guard: falls back.
    simp only [if_pos hqh_hi]
  -- Strict-verdict branches.  Here we need to compute L, R and the
  -- gt192 / le192 dispatch.
  simp only [if_neg hqh_hi]
  -- Introduce kernel intermediates as opaque names.
  set aU : UInt64 := UInt64.ofNat a.toNat with haU_def
  set bU : UInt64 := UInt64.ofNat b.toNat with hbU_def
  set s  : UInt64 := UInt64.ofNat (q + h).toNat with hs_def
  -- L-triple as a `let` we'll case-split.
  set L : UInt64 × UInt64 × UInt64 :=
    (if s < 64 then
       ((0 : UInt64), mulHi64 aU (1 <<< s), aU <<< s)
     else if s < 128 then
       let s64 := s - 64
       if s64 = 0 then ((0 : UInt64), aU, 0)
       else (aU >>> (64 - s64), aU <<< s64, 0)
     else
       let s64 := s - 128
       if s64 = 0 then (aU, (0 : UInt64), 0)
       else (aU <<< s64, 0, 0)) with hL_def
  -- R-triple as opaque bindings.
  set rLo  : UInt64 := bU * gLo with hrLo_def
  set rLoH : UInt64 := mulHi64 bU gLo with hrLoH_def
  set rHi  : UInt64 := bU * gHi with hrHi_def
  set rHiH : UInt64 := mulHi64 bU gHi with hrHiH_def
  set midSum : UInt64 := rHi + rLoH with hmidSum_def
  set midCarry : UInt64 :=
    (if midSum < rHi then (1 : UInt64) else 0) with hmidCarry_def
  set r_hi  : UInt64 := rHiH + midCarry with hr_hi_def
  set r_mid : UInt64 := midSum with hr_mid_def
  set r_lo  : UInt64 := rLo with hr_lo_def
  -- Destructure L into named components.
  obtain ⟨l_hi, l_mid, l_lo⟩ := L
  simp only [] at hL_def
  -- Simplify the (l_hi, l_mid, l_lo).1 / .2.1 / .2.2 in the goal.
  simp only [] -- normalise Prod.mk projections
  -- Bound helpers.
  have ha_toNat_lt_60 : a.toNat < 2 ^ 60 := a_toNat_lt_60 a ha_nn ha_lt
  have hb_toNat_lt_60 : b.toNat < 2 ^ 60 := a_toNat_lt_60 b hb_nn hb_lt
  have ha_toNat_lt_64 : a.toNat < 2 ^ 64 := by
    have : (2 : Nat) ^ 60 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hb_toNat_lt_64 : b.toNat < 2 ^ 64 := by
    have : (2 : Nat) ^ 60 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have haU_toNat : aU.toNat = a.toNat :=
    UInt64_ofNat_toNat_of_lt _ ha_toNat_lt_64
  have hbU_toNat : bU.toNat = b.toNat :=
    UInt64_ofNat_toNat_of_lt _ hb_toNat_lt_64
  have haU_lt_60 : aU.toNat < 2 ^ 60 := haU_toNat.symm ▸ ha_toNat_lt_60
  have hbU_lt_60 : bU.toNat < 2 ^ 60 := hbU_toNat.symm ▸ hb_toNat_lt_60
  -- `q + h` range from kernel guards.
  have hqh_range : 64 ≤ (q + h).toNat ∧ (q + h).toNat ≤ 132 := by
    apply qPlusH_toNat_in_range
    · push_neg at hqh_lo; push_neg; exact hqh_lo
    · push_neg at hqh_hi; push_neg; exact hqh_hi
  obtain ⟨hqpn_lo, hqpn_hi⟩ := hqh_range
  have hqh_nonneg : 0 ≤ q + h := by
    by_contra hp
    push_neg at hp
    have : (q + h).toNat = 0 := Int.toNat_of_nonpos (Int.le_of_lt hp)
    rw [this] at hqpn_lo; omega
  have hqpn_lt_2_64 : (q + h).toNat < 2 ^ 64 := by
    have h264 : (132 : Nat) < 2 ^ 64 := by decide
    omega
  have hs_toNat : s.toNat = (q + h).toNat :=
    UInt64_ofNat_toNat_of_lt _ hqpn_lt_2_64
  -- The kernel's `q + h ≥ 64` guarantee means `s ≥ 64`, so the `s < 64` branch is dead.
  have hs_ge_64 : ¬ s < (64 : UInt64) := by
    rw [UInt64_lt_64_iff]; rw [hs_toNat]; omega
  -- Compute L's triple-Nat value.
  -- Step A: rewrite hL_def using hs_ge_64.
  rw [if_neg hs_ge_64] at hL_def
  -- Now hL_def has the `if s < 128` dispatch.  Case-split.
  have hL_triple_eq : triple192Nat l_hi l_mid l_lo = a.toNat * 2 ^ (q + h).toNat := by
    by_cases hs_128 : s < (128 : UInt64)
    · rw [if_pos hs_128] at hL_def
      have hs_toNat_lt_128 : s.toNat < 128 := by
        rw [UInt64_lt_128_iff] at hs_128; exact hs_128
      set s64 : UInt64 := s - 64 with hs64_def
      have hs64_toNat : s64.toNat = s.toNat - 64 := by
        rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 64 (by decide)
        rw [hs_toNat]; exact hqpn_lo
      -- Reduce hL_def to the inner branches.
      change (l_hi, l_mid, l_lo) =
        (let s64' := s - 64;
         if s64' = 0 then ((0 : UInt64), aU, 0)
         else (aU >>> (64 - s64'), aU <<< s64', 0)) at hL_def
      simp only [← hs64_def] at hL_def
      by_cases hs64_zero : s64 = 0
      · rw [if_pos hs64_zero] at hL_def
        obtain ⟨h1, h2⟩ := Prod.mk.inj hL_def
        obtain ⟨h2', h3⟩ := Prod.mk.inj h2
        subst h1; subst h2'; subst h3
        -- Now l_hi = 0, l_mid = aU, l_lo = 0.
        rw [haU_toNat.symm]
        -- Apply kernel_L_mid_zero (with s64 = 0, qpn = (q+h).toNat).
        have := kernel_L_mid_zero aU s s64 haU_lt_60 (hs_toNat.symm ▸ hqpn_lo)
                  hs_toNat_lt_128 hs64_def hs64_zero (q + h).toNat hs_toNat.symm
        rw [haU_toNat]; rw [haU_toNat] at this
        exact this
      · rw [if_neg hs64_zero] at hL_def
        obtain ⟨h1, h2⟩ := Prod.mk.inj hL_def
        obtain ⟨h2', h3⟩ := Prod.mk.inj h2
        subst h1; subst h2'; subst h3
        -- Now l_hi = aU >>> (64 - s64), l_mid = aU <<< s64, l_lo = 0.
        -- We need to align with kernel_L_mid_nonzero's signature:
        --   triple192Nat (aU >>> UInt64.ofNat (64 - s64.toNat)) (aU <<< s64) 0
        -- but our triple is (aU >>> (64 - s64), aU <<< s64, 0).
        -- The shift-right amount: `64 - s64 : UInt64` vs `UInt64.ofNat (64 - s64.toNat)`.
        -- Bounds: s64.toNat ∈ (0, 64), so 64 - s64.toNat ∈ (0, 64).
        have hs64_lt_64 : s64.toNat < 64 := by
          have : s.toNat < 128 := hs_toNat_lt_128
          omega
        have hs64_pos : 0 < s64.toNat := by
          have : s64.toNat ≠ 0 := by
            intro hz
            apply hs64_zero
            have hbk : s64 = UInt64.ofNat s64.toNat := by
              have hs64_lt_2_64 : s64.toNat < 2 ^ 64 := by omega
              rw [← UInt64.toNat_inj, UInt64_ofNat_toNat_of_lt _ hs64_lt_2_64]
            rw [hbk, hz]; rfl
          omega
        -- Compute (64 - s64 : UInt64).toNat = 64 - s64.toNat.
        have hs64_bk : s64 = UInt64.ofNat s64.toNat := by
          have hs64_lt_2_64 : s64.toNat < 2 ^ 64 := by omega
          rw [← UInt64.toNat_inj, UInt64_ofNat_toNat_of_lt _ hs64_lt_2_64]
        have h64_toNat : (UInt64.ofNat 64 : UInt64).toNat = 64 := by decide
        have h64_eq : (64 : UInt64) = UInt64.ofNat 64 := rfl
        have h64_s64 : (64 - s64 : UInt64).toNat = 64 - s64.toNat := by
          conv => lhs; rw [h64_eq, hs64_bk]
          have := UInt64_sub_toNat_of_ge (UInt64.ofNat 64) s64.toNat (by omega)
                    (by rw [h64_toNat]; omega)
          rw [this, h64_toNat]
        have h_64_s64_ofNat : UInt64.ofNat (64 - s64.toNat) = 64 - s64 := by
          rw [← UInt64.toNat_inj]
          rw [UInt64_ofNat_toNat_of_lt (64 - s64.toNat) (by omega)]
          rw [h64_s64]
        rw [← h_64_s64_ofNat]
        rw [haU_toNat.symm]
        have := kernel_L_mid_nonzero aU s s64 haU_lt_60 (hs_toNat.symm ▸ hqpn_lo)
                  hs_toNat_lt_128 hs64_def hs64_zero (q + h).toNat hs_toNat.symm
        rw [haU_toNat]; rw [haU_toNat] at this
        exact this
    · rw [if_neg hs_128] at hL_def
      have hs_ge_128 : (128 : UInt64) ≤ s := Nat.le_of_not_lt hs_128
      have hs_toNat_ge_128 : 128 ≤ s.toNat := by
        rw [UInt64.le_iff_toNat_le] at hs_ge_128; exact hs_ge_128
      set s64 : UInt64 := s - 128 with hs64_def
      have hs64_toNat : s64.toNat = s.toNat - 128 := by
        rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 128 (by decide) hs_toNat_ge_128
      change (l_hi, l_mid, l_lo) =
        (let s64' := s - 128;
         if s64' = 0 then (aU, (0 : UInt64), 0)
         else (aU <<< s64', 0, 0)) at hL_def
      simp only [← hs64_def] at hL_def
      have hs_toNat_le_132 : s.toNat ≤ 132 := by rw [hs_toNat]; exact hqpn_hi
      by_cases hs64_zero : s64 = 0
      · rw [if_pos hs64_zero] at hL_def
        obtain ⟨h1, h2⟩ := Prod.mk.inj hL_def
        obtain ⟨h2', h3⟩ := Prod.mk.inj h2
        subst h1; subst h2'; subst h3
        rw [haU_toNat.symm]
        have := kernel_L_hi_zero aU s s64 haU_lt_60 hs_toNat_ge_128 hs_toNat_le_132
                  hs64_def hs64_zero (q + h).toNat hs_toNat.symm
        rw [haU_toNat]; rw [haU_toNat] at this
        exact this
      · rw [if_neg hs64_zero] at hL_def
        obtain ⟨h1, h2⟩ := Prod.mk.inj hL_def
        obtain ⟨h2', h3⟩ := Prod.mk.inj h2
        subst h1; subst h2'; subst h3
        rw [haU_toNat.symm]
        have := kernel_L_hi_nonzero aU s s64 haU_lt_60 hs_toNat_ge_128 hs_toNat_le_132
                  hs64_def hs64_zero (q + h).toNat hs_toNat.symm
        rw [haU_toNat]; rw [haU_toNat] at this
        exact this
  -- R-triple Nat value.
  have hR_triple_eq : triple192Nat r_hi r_mid r_lo
                        = b.toNat * (gHi.toNat * 2 ^ 64 + gLo.toNat) := by
    have := kernel_R_eq bU gHi gLo hbU_lt_60
    rw [hbU_toNat] at this
    exact this
  -- Bridge the gHi/gLo references to pow10Lookup128 k.
  -- `hgTuple : (gHi, gLo, h) = pow10Lookup128 k`.
  have hgHi_eq : (pow10Lookup128 k).1 = gHi := by rw [← hgTuple]
  have hgLo_eq : (pow10Lookup128 k).2.1 = gLo := by rw [← hgTuple]
  have hh_eq : (pow10Lookup128 k).2.2 = h := by rw [← hgTuple]
  -- The R-eq spelt in the form needed by the strict bridges.
  have hR_triple_eq' : triple192Nat r_hi r_mid r_lo
                        = b.toNat * ((pow10Lookup128 k).1.toNat * 2 ^ 64
                                      + (pow10Lookup128 k).2.1.toNat) := by
    rw [hgHi_eq, hgLo_eq]; exact hR_triple_eq
  -- Case on gt192.
  by_cases hGt : gt192 l_hi l_mid l_lo r_hi r_mid r_lo = true
  · rw [if_pos hGt]
    -- Apply cmpScaledMixed_strict_plus.
    rw [← cmpScaledMixed_eq_fast]
    exact cmpScaledMixed_strict_plus a q b k l_hi l_mid l_lo r_hi r_mid r_lo
            ha_nn hb_pos hk_lo hk_hi h hh_eq.symm hL_triple_eq hR_triple_eq'
            hqh_nonneg hGt
  · rw [if_neg hGt]
    -- gt192 is false.
    have hGt_false : gt192 l_hi l_mid l_lo r_hi r_mid r_lo = false := by
      cases h_eq : gt192 l_hi l_mid l_lo r_hi r_mid r_lo with
      | true => exact absurd h_eq hGt
      | false => rfl
    -- Now case on le192.
    by_cases hLe : le192 (add192_64 l_hi l_mid l_lo bU).1
                          (add192_64 l_hi l_mid l_lo bU).2.1
                          (add192_64 l_hi l_mid l_lo bU).2.2
                          r_hi r_mid r_lo = true
    · rw [if_pos hLe]
      -- Apply cmpScaledMixed_strict_minus.
      rw [← cmpScaledMixed_eq_fast]
      exact cmpScaledMixed_strict_minus a q b k l_hi l_mid l_lo r_hi r_mid r_lo bU
              ha_nn hb_pos hb_lt hbU_toNat hk_lo hk_hi h hh_eq.symm
              hL_triple_eq hR_triple_eq' hqh_nonneg hGt_false hLe
    · rw [if_neg hLe]

@[csimp]
theorem cmpScaledMixed_eq_fast_csimp : @cmpScaledMixed = @cmpScaledMixed_fast2 := by
  funext a q b k
  exact cmpScaledMixed_eq_fast2 a q b k

/-! ## Easy guard-fallback branches of `shiftedSig_eq_fast2`

When any of the kernel guards fail (m ≥ 2^60, kLookup out of table range,
or shiftAmt out of [124, 192)), the kernel falls back to `shiftedSig_fast`,
which equals `shiftedSig` by `shiftedSig_eq_fast`. -/

/-- Reduce `shiftedSig_fast2 m q k` to `shiftedSig_fast m q k` when the
    kernel's early guards fire (m ≥ 2^60, k out of table range,
    shiftAmt out of [124, 192), or the safe-regime guard
    `B = 2^qNeg · 10^kPos ≥ 2^64` fires). -/
theorem shiftedSig_fast2_guards
    (m : Nat) (q k : Int)
    (hGuard : m ≥ (1 <<< 60 : Nat) ∨
              -k < pow10Table128_kMin ∨ -k > pow10Table128_kMax ∨
              ((pow10Lookup128 (-k)).2.2 - q) < 124 ∨
              ((pow10Lookup128 (-k)).2.2 - q) ≥ 192 ∨
              (2 ^ (if q < 0 then (-q).toNat else 0) *
                10 ^ (if k ≥ 0 then k.toNat else 0)) ≥ (1 <<< 64 : Nat)) :
    shiftedSig_fast2 m q k = shiftedSig_fast m q k := by
  unfold shiftedSig_fast2
  rcases hGuard with h | h | h | h | h | h
  · simp only [if_pos h]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [if_pos h1]
    · simp only [if_neg h1, if_pos (Or.inl h)]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [if_pos h1]
    · simp only [if_neg h1, if_pos (Or.inr h)]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [if_pos h1]
    · by_cases h2 : (-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax
      · simp only [if_neg h1, if_pos h2]
      · simp only [if_neg h1, if_neg h2]
        -- h : (pow10Lookup128 (-k)).2.2 - q < 124.  We want the kernel's
        -- destructured (gHi, gLo, h_t) view; the .2.2 projection of the
        -- destructured tuple matches h_t in the goal.
        have hk : ((pow10Lookup128 (-k)).2.2 - q < 124 ∨
                   (pow10Lookup128 (-k)).2.2 - q ≥ 192) := Or.inl h
        rw [show (pow10Lookup128 (-k)) =
              ((pow10Lookup128 (-k)).1, (pow10Lookup128 (-k)).2.1, (pow10Lookup128 (-k)).2.2) from rfl]
        simp only [if_pos hk]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [if_pos h1]
    · by_cases h2 : (-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax
      · simp only [if_neg h1, if_pos h2]
      · simp only [if_neg h1, if_neg h2]
        have hk : ((pow10Lookup128 (-k)).2.2 - q < 124 ∨
                   (pow10Lookup128 (-k)).2.2 - q ≥ 192) := Or.inr h
        rw [show (pow10Lookup128 (-k)) =
              ((pow10Lookup128 (-k)).1, (pow10Lookup128 (-k)).2.1, (pow10Lookup128 (-k)).2.2) from rfl]
        simp only [if_pos hk]
  · -- New safe-regime guard: B = 2^qNeg · 10^kPos ≥ 2^64.
    by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [if_pos h1]
    · by_cases h2 : (-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax
      · simp only [if_neg h1, if_pos h2]
      · by_cases h3 : ((pow10Lookup128 (-k)).2.2 - q < 124 ∨
                       (pow10Lookup128 (-k)).2.2 - q ≥ 192)
        · simp only [if_neg h1, if_neg h2]
          rw [show (pow10Lookup128 (-k)) =
                ((pow10Lookup128 (-k)).1, (pow10Lookup128 (-k)).2.1, (pow10Lookup128 (-k)).2.2) from rfl]
          simp only [if_pos h3]
        · simp only [if_neg h1, if_neg h2]
          rw [show (pow10Lookup128 (-k)) =
                ((pow10Lookup128 (-k)).1, (pow10Lookup128 (-k)).2.1, (pow10Lookup128 (-k)).2.2) from rfl]
          simp only [if_neg h3, if_pos h]

/-! ## Floor equality `shiftedSig = shiftedSig_fast2`

The unsafe sub-regime (where `m · B > 2^s` without the Schubfach §9.7
residue argument) is avoided at runtime by the safe-regime guard
`B = 2^qNeg · 10^kPos < 2^64`.  Combined with `m < 2^60` and `s ≥ 124`,
this gives `m · B < 2^124 ≤ 2^s`, the regime where `shiftedSig_floor_safe`
proves the kernel floor equals the spec floor.  Inputs that fail the
guard fall back to `shiftedSig_fast` (which equals `shiftedSig` by
`shiftedSig_eq_fast`), preserving correctness universally. -/

set_option maxRecDepth 4000 in
theorem shiftedSig_eq_fast2 (m : Nat) (q k : Int) :
    shiftedSig m q k = shiftedSig_fast2 m q k := by
  -- Stage 1: dispatch all guard branches to `shiftedSig_fast = shiftedSig`.
  by_cases hm60 : m ≥ (1 <<< 60 : Nat)
  · rw [shiftedSig_eq_fast]
    exact (shiftedSig_fast2_guards m q k (Or.inl hm60)).symm
  by_cases hk : (-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax
  · rw [shiftedSig_eq_fast]
    rcases hk with h | h
    · exact (shiftedSig_fast2_guards m q k (Or.inr (Or.inl h))).symm
    · exact (shiftedSig_fast2_guards m q k (Or.inr (Or.inr (Or.inl h)))).symm
  by_cases hs : (pow10Lookup128 (-k)).2.2 - q < 124 ∨ (pow10Lookup128 (-k)).2.2 - q ≥ 192
  · rw [shiftedSig_eq_fast]
    rcases hs with h | h
    · exact (shiftedSig_fast2_guards m q k (Or.inr (Or.inr (Or.inr (Or.inl h))))).symm
    · exact (shiftedSig_fast2_guards m q k
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).symm
  by_cases hB64 :
      (2 ^ (if q < 0 then (-q).toNat else 0) *
        10 ^ (if k ≥ 0 then k.toNat else 0)) ≥ (1 <<< 64 : Nat)
  · rw [shiftedSig_eq_fast]
    exact (shiftedSig_fast2_guards m q k
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hB64)))))).symm
  -- Stage 2: safe-regime case.  All guards passed.
  push_neg at hm60 hk hs hB64
  obtain ⟨hkLo, hkHi⟩ := hk
  obtain ⟨hsLo, hsHi⟩ := hs
  -- Unfold both sides; bind opaque names for shared subterms.
  have hm60_not : ¬ m ≥ (1 <<< 60 : Nat) := by omega
  have hk_not : ¬ ((-k : Int) < pow10Table128_kMin ∨ (-k : Int) > pow10Table128_kMax) := by
    push_neg; exact ⟨hkLo, hkHi⟩
  have hs_not : ¬ ((pow10Lookup128 (-k)).2.2 - q < 124 ∨
                   (pow10Lookup128 (-k)).2.2 - q ≥ 192) := by
    push_neg; exact ⟨hsLo, hsHi⟩
  have hB_not : ¬ ((2 ^ (if q < 0 then (-q).toNat else 0) *
                     10 ^ (if k ≥ 0 then k.toNat else 0)) ≥ (1 <<< 64 : Nat)) := by omega
  unfold shiftedSig_fast2
  rw [if_neg hm60_not]
  rw [if_neg hk_not]
  rw [show (pow10Lookup128 (-k)) =
        ((pow10Lookup128 (-k)).1, (pow10Lookup128 (-k)).2.1,
         (pow10Lookup128 (-k)).2.2) from rfl]
  simp only [if_neg hs_not]
  simp only [if_neg hB_not]
  -- Introduce kernel intermediates.
  set gHi : UInt64 := (pow10Lookup128 (-k)).1 with hgHi_def
  set gLo : UInt64 := (pow10Lookup128 (-k)).2.1 with hgLo_def
  set h_t : Int := (pow10Lookup128 (-k)).2.2 with hh_def
  set shiftAmt : Int := h_t - q with hshiftAmt_def
  set mU : UInt64 := UInt64.ofNat m with hmU_def
  set s : UInt64 := UInt64.ofNat shiftAmt.toNat with hs_def
  -- Bounds.
  have hshiftAmt_nn : 0 ≤ shiftAmt := by rw [hshiftAmt_def]; omega
  have hshiftAmt_lo : 124 ≤ shiftAmt := by rw [hshiftAmt_def]; omega
  have hshiftAmt_hi : shiftAmt < 192 := by rw [hshiftAmt_def]; omega
  have hshiftAmt_toNat_lo : 124 ≤ shiftAmt.toNat := by
    have := Int.toNat_of_nonneg hshiftAmt_nn
    omega
  have hshiftAmt_toNat_hi : shiftAmt.toNat < 192 := by
    have := Int.toNat_of_nonneg hshiftAmt_nn
    omega
  have hshiftAmt_lt_2_64 : shiftAmt.toNat < 2 ^ 64 := by
    have h264 : (192 : Nat) < 2 ^ 64 := by decide
    omega
  have hs_toNat : s.toNat = shiftAmt.toNat :=
    UInt64_ofNat_toNat_of_lt _ hshiftAmt_lt_2_64
  -- m fits in UInt64.
  have hm_lt_60 : m < 2 ^ 60 := by
    have : (1 <<< 60 : Nat) = 2 ^ 60 := by decide
    omega
  have hm_lt_64 : m < 2 ^ 64 := by
    have : (2 : Nat) ^ 60 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hmU_toNat : mU.toNat = m := UInt64_ofNat_toNat_of_lt _ hm_lt_64
  have hmU_lt_60 : mU.toNat < 2 ^ 60 := hmU_toNat.symm ▸ hm_lt_60
  -- Bind kernel triple (rHi, rMid, rLo) and the high carry.
  set pLo  : UInt64 := mU * gLo with hpLo_def
  set pLoH : UInt64 := mulHi64 mU gLo with hpLoH_def
  set pHi  : UInt64 := mU * gHi with hpHi_def
  set pHiH : UInt64 := mulHi64 mU gHi with hpHiH_def
  set midSum : UInt64 := pHi + pLoH with hmidSum_def
  set midCarry : UInt64 := if midSum < pHi then (1 : UInt64) else 0 with hmidCarry_def
  set rHi  : UInt64 := pHiH + midCarry with hrHi_def
  set rMid : UInt64 := midSum with hrMid_def
  set rLo  : UInt64 := pLo with hrLo_def
  -- Triple value: triple192Nat rHi rMid rLo = m * G  (exact, because m < 2^60).
  have hTriple : triple192Nat rHi rMid rLo = m * (gHi.toNat * 2 ^ 64 + gLo.toNat) := by
    have := kernel_R_eq mU gHi gLo hmU_lt_60
    rw [hmU_toNat] at this
    exact this
  -- The `s < 64` branch is dead because shiftAmt ≥ 124 > 64.
  have hs_ge_64 : ¬ s < (64 : UInt64) := by
    rw [UInt64_lt_64_iff]; rw [hs_toNat]; omega
  -- Reduce the kernel: drop the `s < 64` branch.
  simp only [if_neg hs_ge_64]
  -- Establish the bound `rHi.toNat < 2^60`.
  have hG_lt : gHi.toNat * 2 ^ 64 + gLo.toNat < 2 ^ 128 := by
    have hgHi_lt : gHi.toNat < 2 ^ 64 := gHi.toNat_lt
    have hgLo_lt : gLo.toNat < 2 ^ 64 := gLo.toNat_lt
    have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
    have h1 : gHi.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
      apply Nat.mul_le_mul_right; omega
    have h2 : (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 64 * 2 ^ 64 := by
      have hpow_pos : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
      have : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
        rw [Nat.sub_mul]
      omega
    omega
  have hMG_lt : m * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 188 := by
    have : m * (gHi.toNat * 2 ^ 64 + gLo.toNat) < 2 ^ 60 * 2 ^ 128 :=
      Nat.mul_lt_mul_of_lt_of_lt hm_lt_60 hG_lt
    have h60_128 : (2 : Nat) ^ 60 * 2 ^ 128 = 2 ^ 188 := by
      rw [← Nat.pow_add]
    omega
  have hTriple_lt : triple192Nat rHi rMid rLo < 2 ^ 188 := by
    rw [hTriple]; exact hMG_lt
  -- From triple < 2^188 and triple = rHi · 2^128 + rMid · 2^64 + rLo with each < 2^64,
  -- we get rHi.toNat ≤ 2^60.  Actually rHi.toNat · 2^128 ≤ triple < 2^188, so rHi < 2^60.
  have hrHi_lt_60 : rHi.toNat < 2 ^ 60 := by
    have : rHi.toNat * 2 ^ 128 ≤ triple192Nat rHi rMid rLo := by
      unfold triple192Nat; omega
    have : rHi.toNat * 2 ^ 128 < 2 ^ 188 := by omega
    have hpow : (2 : Nat) ^ 188 = 2 ^ 60 * 2 ^ 128 := by
      rw [← Nat.pow_add]
    rw [hpow] at this
    exact Nat.lt_of_mul_lt_mul_right this
  -- Show kernel RHS equals triple / 2^shiftAmt.toNat by case-splitting on s.
  have hKernel_eq : (if s < 128 then
                       if s - 64 = 0 then rMid
                       else rMid >>> (s - 64) ||| rHi <<< (64 - (s - 64))
                     else rHi >>> (s - 128)).toNat
                    = triple192Nat rHi rMid rLo / 2 ^ shiftAmt.toNat := by
    by_cases hs_128 : s < (128 : UInt64)
    · rw [if_pos hs_128]
      have hs_toNat_lt_128 : s.toNat < 128 := by
        rw [UInt64_lt_128_iff] at hs_128; exact hs_128
      have hs_toNat_ge_64 : 64 ≤ s.toNat := by rw [hs_toNat]; omega
      -- s - 64 ≠ 0 because s.toNat ∈ [124, 128) so s.toNat - 64 ∈ [60, 64).
      set s64 : UInt64 := s - 64 with hs64_def
      have hs64_toNat : s64.toNat = s.toNat - 64 := by
        rw [hs64_def]; apply UInt64_sub_toNat_of_ge s 64 (by decide) hs_toNat_ge_64
      have hs64_lo : 60 ≤ s64.toNat := by rw [hs64_toNat, hs_toNat]; omega
      have hs64_lt_64 : s64.toNat < 64 := by rw [hs64_toNat, hs_toNat]; omega
      have hs64_pos : 0 < s64.toNat := by omega
      have hs64_nz : s64 ≠ 0 := by
        intro hz
        have : s64.toNat = 0 := by rw [hz]; rfl
        omega
      rw [if_neg hs64_nz]
      -- Apply shift_kernel_extract_mid.
      have hrHi_lt_s64 : rHi.toNat < 2 ^ s64.toNat := by
        have h60_le : (2 : Nat) ^ 60 ≤ 2 ^ s64.toNat := Nat.pow_le_pow_right (by decide) hs64_lo
        omega
      have := shift_kernel_extract_mid rHi rMid rLo s s64
                hs_toNat_ge_64 hs_toNat_lt_128 hs64_def hs64_nz hrHi_lt_s64
      rw [hs_toNat] at this
      exact this
    · rw [if_neg hs_128]
      have hs_toNat_ge_128 : 128 ≤ s.toNat := by
        by_contra hp; push_neg at hp
        apply hs_128
        rw [UInt64_lt_128_iff]; exact hp
      have hs_toNat_lt_192 : s.toNat < 192 := by rw [hs_toNat]; omega
      set s64 : UInt64 := s - 128 with hs64_def
      have := shift_kernel_extract_hi rHi rMid rLo s s64
                hs_toNat_ge_128 hs_toNat_lt_192 hs64_def
      rw [hs_toNat] at this
      exact this
  -- Now reduce the goal to `shiftedSig m q k = triple / 2^shiftAmt.toNat`.
  rw [hKernel_eq, hTriple]
  -- m = 0 case is trivial.
  by_cases hm0 : m = 0
  · subst hm0
    unfold shiftedSig
    simp
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  -- Spec side via shiftedSig_eq_fast.
  rw [shiftedSig_eq_fast]
  unfold shiftedSig_fast
  simp only [pow2Lookup_eq, pow10Lookup_eq]
  -- Set q/k signed splits.
  set qPos : Nat := if q ≥ 0 then q.toNat else 0 with hqPos_def
  set qNeg : Nat := if q < 0 then (-q).toNat else 0 with hqNeg_def
  set kPos : Nat := if k ≥ 0 then k.toNat else 0 with hkPos_def
  set kNeg : Nat := if k < 0 then (-k).toNat else 0 with hkNeg_def
  -- The h_t / shiftAmt = h_t - q splits via the sign of h_t.
  set hPos : Nat := if h_t ≥ 0 then h_t.toNat else 0 with hhPos_def
  set hNeg : Nat := if h_t < 0 then (-h_t).toNat else 0 with hhNeg_def
  set G : Nat := gHi.toNat * 2 ^ 64 + gLo.toNat with hG_def
  set B : Nat := 2 ^ qNeg * 10 ^ kPos with hB_def
  set N : Nat := m * 2 ^ qPos * 10 ^ kNeg with hN_def
  -- B > 0.
  have hB_pos : 0 < B := by
    rw [hB_def]; exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by decide))
  -- B < 2^64 (the safe-regime guard).
  have hB_lt_64 : B < 2 ^ 64 := by
    rw [hB_def]
    have : (1 <<< 64 : Nat) = 2 ^ 64 := by decide
    have := hB64
    omega
  -- Goal currently: N / B = m * G / 2^shiftAmt.toNat.
  -- Apply shiftedSig_floor_safe with sandwich + safety.
  -- The power regrouping identity:
  --   2^shiftAmt.toNat · 2^qPos · 2^hNeg = 2^qNeg · 2^hPos
  -- We derive it from `shiftAmt = h_t - q` ↔ `shiftAmt + qPos + hNeg = qNeg + hPos`.
  have hregroup_eq : shiftAmt.toNat + qPos + hNeg = qNeg + hPos := by
    have hShiftAmt_int : (shiftAmt.toNat : Int) = shiftAmt := Int.toNat_of_nonneg hshiftAmt_nn
    -- Prove the Int form via case analysis on signs of q and h_t.
    have hIntEq : (shiftAmt.toNat : Int) + (qPos : Int) + (hNeg : Int)
                    = (qNeg : Int) + (hPos : Int) := by
      rw [hShiftAmt_int]
      have hShift_eq : shiftAmt = h_t - q := hshiftAmt_def
      rw [hShift_eq]
      rw [hqPos_def, hqNeg_def, hhPos_def, hhNeg_def]
      by_cases hq : q ≥ 0
      · have hq_neg : ¬ q < 0 := by omega
        have hqtoNat : (q.toNat : Int) = q := Int.toNat_of_nonneg hq
        rw [if_pos hq, if_neg hq_neg]
        push_cast
        -- h_t ≥ q (since h_t - q ≥ 124 ≥ 0).
        have hh_nn : 0 ≤ h_t := by
          have : 124 ≤ h_t - q := hsLo
          omega
        have hh_neg : ¬ h_t < 0 := by omega
        have hhtoNat : (h_t.toNat : Int) = h_t := Int.toNat_of_nonneg hh_nn
        rw [if_pos hh_nn, if_neg hh_neg]
        rw [hqtoNat, hhtoNat]; grind
      · push_neg at hq
        have hq_lt : q < 0 := hq
        have hq_nn : ¬ q ≥ 0 := by omega
        have hqtoNat : ((-q).toNat : Int) = -q := Int.toNat_of_nonneg (by omega)
        rw [if_neg hq_nn, if_pos hq_lt]
        rw [hqtoNat]
        by_cases hh : h_t ≥ 0
        · have hh_neg : ¬ h_t < 0 := by omega
          have hhtoNat : (h_t.toNat : Int) = h_t := Int.toNat_of_nonneg hh
          rw [if_pos hh, if_neg hh_neg]
          rw [hhtoNat]; push_cast; grind
        · push_neg at hh
          have hh_nn : ¬ h_t ≥ 0 := by omega
          have hhtoNat : ((-h_t).toNat : Int) = -h_t := Int.toNat_of_nonneg (by omega)
          rw [if_neg hh_nn, if_pos hh]
          rw [hhtoNat]; push_cast; grind
    -- Lift Int equation to Nat.
    have hL : ((shiftAmt.toNat + qPos + hNeg : Nat) : Int)
                = ((qNeg + hPos : Nat) : Int) := by
      push_cast
      omega
    exact_mod_cast hL
  have hRegroup : 2 ^ shiftAmt.toNat * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos :=
    two_pow_regroup shiftAmt.toNat qNeg qPos hPos hNeg
      (by have := hregroup_eq; omega)
  -- Table invariant: G satisfies the ceiling bound.
  have hInv := pow10Lookup128_invariant (-k) hkLo hkHi
  -- The invariant uses kPos' = if -k ≥ 0 then (-k).toNat else 0, etc.
  -- For us: when k ≤ 0, kPos' = (-k).toNat = kNeg.  When k > 0, kPos' = 0 = kNeg.
  -- So kPos' = kNeg (ours) and kNeg' = kPos (ours).  Convert:
  have hkPos'_eq_kNeg : (if (-k : Int) ≥ 0 then (-k).toNat else 0) = kNeg := by
    rw [hkNeg_def]
    by_cases hk_nn : k ≥ 0
    · by_cases hk_pos : k = 0
      · subst hk_pos; simp
      · have hk_pos' : k > 0 := by omega
        have h_neg_k_lt : -k < 0 := by omega
        have h_neg_k_not_nn : ¬ (-k : Int) ≥ 0 := by omega
        have h_k_not_lt_0 : ¬ k < 0 := by omega
        rw [if_neg h_neg_k_not_nn, if_neg h_k_not_lt_0]
    · push_neg at hk_nn
      have h_neg_k_nn : (-k : Int) ≥ 0 := by omega
      have h_k_lt_0 : k < 0 := hk_nn
      rw [if_pos h_neg_k_nn, if_pos h_k_lt_0]
  have hkNeg'_eq_kPos : (if (-k : Int) < 0 then (-(-k)).toNat else 0) = kPos := by
    rw [hkPos_def]
    by_cases hk_nn : k ≥ 0
    · by_cases hk_zero : k = 0
      · subst hk_zero; simp
      · have hk_pos : k > 0 := by omega
        have h_neg_k_lt : (-k : Int) < 0 := by omega
        have hk_nn' : k ≥ 0 := hk_nn
        rw [if_pos h_neg_k_lt, if_pos hk_nn']
        have : -(-k) = k := by grind
        rw [this]
    · push_neg at hk_nn
      have h_neg_k_nn : ¬ (-k : Int) < 0 := by omega
      have hk_nn_not : ¬ k ≥ 0 := by omega
      rw [if_neg h_neg_k_nn, if_neg hk_nn_not]
  -- Specialise the invariant to our names.
  have hG_eq : (pow10Lookup128 (-k)).1.toNat * 2 ^ 64 + (pow10Lookup128 (-k)).2.1.toNat = G := by
    rw [hG_def, ← hgHi_def, ← hgLo_def]
  have hh_t_eq : (pow10Lookup128 (-k)).2.2 = h_t := by rw [← hh_def]
  -- Sandwich from the invariant.
  have hInv' : 10 ^ kNeg * 2 ^ hPos ≤ G * 10 ^ kPos * 2 ^ hNeg
              ∧ G * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg := by
    have h1 := hInv
    simp only at h1
    -- h1 uses kPos' / kNeg' / hPos' / hNeg' for the -k lookup; translate.
    have hkPos'_eq : (if (-k : Int) ≥ 0 then (-k).toNat else 0) = kNeg := hkPos'_eq_kNeg
    have hkNeg'_eq : (if (-k : Int) < 0 then (-(-k)).toNat else 0) = kPos := hkNeg'_eq_kPos
    have hhPos'_eq : (if (pow10Lookup128 (-k)).2.2 ≥ 0 then ((pow10Lookup128 (-k)).2.2).toNat else 0)
                      = hPos := by
      rw [hhPos_def, hh_t_eq]
    have hhNeg'_eq : (if (pow10Lookup128 (-k)).2.2 < 0 then
                        (-(pow10Lookup128 (-k)).2.2).toNat else 0) = hNeg := by
      rw [hhNeg_def, hh_t_eq]
    rw [hkPos'_eq, hkNeg'_eq, hhPos'_eq, hhNeg'_eq, hG_eq] at h1
    exact h1
  -- Apply shiftedSig_sandwich.
  have hSandwich := shiftedSig_sandwich m G qPos qNeg kPos kNeg hPos hNeg shiftAmt.toNat
                      hm_pos hRegroup hInv'
  -- Safety: m * B ≤ 2^shiftAmt.toNat.
  have hSafe : m * B ≤ 2 ^ shiftAmt.toNat := by
    have h1 : m * B < 2 ^ 60 * 2 ^ 64 := Nat.mul_lt_mul_of_lt_of_lt hm_lt_60 hB_lt_64
    have h2 : (2 : Nat) ^ 60 * 2 ^ 64 = 2 ^ 124 := by rw [← Nat.pow_add]
    have h3 : (2 : Nat) ^ 124 ≤ 2 ^ shiftAmt.toNat :=
      Nat.pow_le_pow_right (by decide) hshiftAmt_toNat_lo
    omega
  -- Floor equality.
  have hFloor := shiftedSig_floor_safe m G B shiftAmt.toNat N hB_pos hSafe hSandwich
  -- Goal: N / B = m * G / 2^shiftAmt.toNat.
  exact hFloor.symm

@[csimp]
theorem shiftedSig_eq_fast_csimp : @shiftedSig = @shiftedSig_fast2 := by
  funext m q k
  exact shiftedSig_eq_fast2 m q k

end Srtfp.Schubfach
