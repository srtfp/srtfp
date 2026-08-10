/- Correctness of the 256-bit (4-limb) multiply-shift kernel `shiftedSig_v4`.

   Mirrors `KernelCorrectness.lean` (128-bit) but for the 192-bit table and
   256-bit multiply.  The proof structure follows
   `shiftedSig_eq_fast2` exactly: sandwich + slack + safe-regime, where the
   safe regime is widened to `B = 2^qNeg · 10^kPos < 2^128` (vs the 128-bit
   kernel's `B < 2^64`) thanks to 64 more bits of table precision.

   Key milestones:
   - `quad256Nat`/`mul256_b_g_toNat`: 4-limb mul correctness.
   - `shift_kernel256_*_eq`: 256-bit right-shift extraction lemmas.
   - `shiftedSig_v4_guards`: guard-fallback reduction.
   - `shiftedSig_v4_eq`: floor equality `shiftedSig_v4 m q k = shiftedSig m q k`.

   The 192-bit-precision sandwich/slack lemmas (`shiftedSig_sandwich_192`,
   etc.) are obtained by re-using `shiftedSig_sandwich` (parametric in the
   precision) with `g ≥ 2^191` from `pow10Lookup192_g_ge`.
-/
import Srtfp.Schubfach.Perf.Uint64Kernel192
import Srtfp.Schubfach.Perf.Uint64Kernel
import Srtfp.Schubfach.Perf.Uint64Bridge
import Srtfp.Schubfach.KernelCorrectness
import Srtfp.Schubfach.Perf.TableInvariant192
import Srtfp.Tactics

namespace Srtfp.Schubfach

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! ## 4-limb Nat interpretation -/

/-- Nat value of a 256-bit (hi, midHi, midLo, lo) UInt64 quadruple. -/
def quad256Nat (hi midHi midLo lo : UInt64) : Nat :=
  hi.toNat * 2 ^ 192 + midHi.toNat * 2 ^ 128 + midLo.toNat * 2 ^ 64 + lo.toNat

theorem quad256Nat_lt (hi midHi midLo lo : UInt64) :
    quad256Nat hi midHi midLo lo < 2 ^ 256 := by
  unfold quad256Nat
  have hHi : hi.toNat < 2 ^ 64 := hi.toNat_lt
  have hMH : midHi.toNat < 2 ^ 64 := midHi.toNat_lt
  have hML : midLo.toNat < 2 ^ 64 := midLo.toNat_lt
  have hLo : lo.toNat < 2 ^ 64 := lo.toNat_lt
  have h192 : (2 : Nat) ^ 192 = 2 ^ 64 * (2 ^ 64 * 2 ^ 64) := by decide
  have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
  have h256 : (2 : Nat) ^ 256 = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by decide
  grind

/-! ## 4-limb mul correctness via `mul192_b_g_toNat` + shift

The kernel's 4-limb product can be derived from two 128-bit muls plus
carry bookkeeping:

  m · g192  =  m · gHi · 2^128  +  m · (gMid · 2^64 + gLo)

The right summand is a 192-bit value (since m < 2^60 < 2^64 and the
inner factor < 2^128, product < 2^192), exactly what `mul192_b_g_toNat`
computes for `(mU, gMid, gLo)`.  Call its triple `(rHi, rMid, rLo)`.

The left summand `m · gHi` is a 128-bit value (m, gHi < 2^64).
Its low 64 bits live at position 128 in the final 256-bit product;
its high 64 bits live at position 192.

Adding `(m · gHi) · 2^128` to the triple `(0, rHi, rMid, rLo)` (interpreted
as a 256-bit value with top limb 0):
  - `rLo` unchanged
  - `rMid` unchanged
  - `rHi + (m · gHi mod 2^64)` → new mid-high limb, with carry
  - `0 + (m · gHi / 2^64) + carry` → new top limb

This is exactly what the kernel computes.
-/

/-- The 4-limb kernel computes `m · (gHi·2^128 + gMid·2^64 + gLo)`
    exactly (no modular wrap), provided `m < 2^60`. -/
theorem shiftedSig_u192_kernel_mul_eq
    (mU gHi gMid gLo : UInt64) (hm : mU.toNat < 2 ^ 60) :
    let pLoLo  : UInt64 := mU * gLo
    let pLoHi  : UInt64 := mulHi64 mU gLo
    let pMidLo : UInt64 := mU * gMid
    let pMidHi : UInt64 := mulHi64 mU gMid
    let pHiLo  : UInt64 := mU * gHi
    let pHiHi  : UInt64 := mulHi64 mU gHi
    let s1 : UInt64 := pLoHi + pMidLo
    let c1 : UInt64 := if s1 < pLoHi then 1 else 0
    let qMidLo : UInt64 := s1
    let s2a : UInt64 := pMidHi + pHiLo
    let c2a : UInt64 := if s2a < pMidHi then 1 else 0
    let s2b : UInt64 := s2a + c1
    let c2b : UInt64 := if s2b < s2a then 1 else 0
    let qMidHi : UInt64 := s2b
    let carryToHi : UInt64 := c2a + c2b
    let qHi : UInt64 := pHiHi + carryToHi
    let qLo : UInt64 := pLoLo
    quad256Nat qHi qMidHi qMidLo qLo
      = mU.toNat * (gHi.toNat * 2 ^ 128 + gMid.toNat * 2 ^ 64 + gLo.toNat) := by
  -- Component bounds.
  have hm_lt_64 : mU.toNat < 2 ^ 64 := by
    have : (2 : Nat) ^ 60 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hgH : gHi.toNat < 2 ^ 64 := gHi.toNat_lt
  have hgM : gMid.toNat < 2 ^ 64 := gMid.toNat_lt
  have hgL : gLo.toNat < 2 ^ 64 := gLo.toNat_lt
  -- Each m · g_limb < 2^60 · 2^64 = 2^124.
  have hMul_lt_124 : ∀ (x : UInt64), x.toNat < 2 ^ 64 →
      mU.toNat * x.toNat < 2 ^ 124 := by
    intros x hx
    have : mU.toNat * x.toNat < 2 ^ 60 * 2 ^ 64 :=
      Nat.mul_lt_mul_of_lt_of_lt hm hx
    have h124 : (2 : Nat) ^ 60 * 2 ^ 64 = 2 ^ 124 := by decide
    omega
  -- mulHi/mul splits.
  have hPLoLo : (mU * gLo).toNat = (mU.toNat * gLo.toNat) % 2 ^ 64 := UInt64.toNat_mul mU gLo
  have hPLoHi : (mulHi64 mU gLo).toNat = mU.toNat * gLo.toNat / 2 ^ 64 :=
    mulHi64_toNat_eq mU gLo
  have hPMidLo : (mU * gMid).toNat = (mU.toNat * gMid.toNat) % 2 ^ 64 := UInt64.toNat_mul mU gMid
  have hPMidHi : (mulHi64 mU gMid).toNat = mU.toNat * gMid.toNat / 2 ^ 64 :=
    mulHi64_toNat_eq mU gMid
  have hPHiLo : (mU * gHi).toNat = (mU.toNat * gHi.toNat) % 2 ^ 64 := UInt64.toNat_mul mU gHi
  have hPHiHi : (mulHi64 mU gHi).toNat = mU.toNat * gHi.toNat / 2 ^ 64 :=
    mulHi64_toNat_eq mU gHi
  -- Bounds on mulHi64-results (high limb is < 2^60 since the product is < 2^124).
  have hPLoHi_lt_60 : (mulHi64 mU gLo).toNat < 2 ^ 60 := by
    rw [hPLoHi]
    have := hMul_lt_124 gLo hgL
    have h60_64 : (2 : Nat) ^ 124 = 2 ^ 60 * 2 ^ 64 := by decide
    exact Nat.div_lt_of_lt_mul (by rw [h60_64] at this; exact this)
  have hPMidHi_lt_60 : (mulHi64 mU gMid).toNat < 2 ^ 60 := by
    rw [hPMidHi]
    have := hMul_lt_124 gMid hgM
    have h60_64 : (2 : Nat) ^ 124 = 2 ^ 60 * 2 ^ 64 := by decide
    exact Nat.div_lt_of_lt_mul (by rw [h60_64] at this; exact this)
  have hPHiHi_lt_60 : (mulHi64 mU gHi).toNat < 2 ^ 60 := by
    rw [hPHiHi]
    have := hMul_lt_124 gHi hgH
    have h60_64 : (2 : Nat) ^ 124 = 2 ^ 60 * 2 ^ 64 := by decide
    exact Nat.div_lt_of_lt_mul (by rw [h60_64] at this; exact this)
  -- Set the abbreviations to match the goal statement.
  set pLoLo  : UInt64 := mU * gLo
  set pLoHi  : UInt64 := mulHi64 mU gLo
  set pMidLo : UInt64 := mU * gMid
  set pMidHi : UInt64 := mulHi64 mU gMid
  set pHiLo  : UInt64 := mU * gHi
  set pHiHi  : UInt64 := mulHi64 mU gHi
  set s1 : UInt64 := pLoHi + pMidLo
  set c1 : UInt64 := if s1 < pLoHi then (1 : UInt64) else 0
  set qMidLo : UInt64 := s1
  set s2a : UInt64 := pMidHi + pHiLo
  set c2a : UInt64 := if s2a < pMidHi then (1 : UInt64) else 0
  set s2b : UInt64 := s2a + c1
  set c2b : UInt64 := if s2b < s2a then (1 : UInt64) else 0
  set qMidHi : UInt64 := s2b
  set carryToHi : UInt64 := c2a + c2b
  set qHi : UInt64 := pHiHi + carryToHi
  set qLo : UInt64 := pLoLo
  -- Auxiliary Nat values to keep the algebra readable.
  -- α = m·gLo, β = m·gMid, γ = m·gHi (each < 2^124)
  let α : Nat := mU.toNat * gLo.toNat
  let β : Nat := mU.toNat * gMid.toNat
  let γ : Nat := mU.toNat * gHi.toNat
  -- Split each into hi/lo limbs (each < 2^64; the hi part < 2^60).
  let αHi : Nat := α / 2 ^ 64
  let αLo : Nat := α % 2 ^ 64
  let βHi : Nat := β / 2 ^ 64
  let βLo : Nat := β % 2 ^ 64
  let γHi : Nat := γ / 2 ^ 64
  let γLo : Nat := γ % 2 ^ 64
  -- Splits.
  have h64_pos : (0 : Nat) < 2 ^ 64 := Nat.two_pow_pos _
  have hα_split : α = αHi * 2 ^ 64 + αLo := by
    show α = α / 2 ^ 64 * 2 ^ 64 + α % 2 ^ 64
    have := Nat.div_add_mod α (2 ^ 64); omega
  have hβ_split : β = βHi * 2 ^ 64 + βLo := by
    show β = β / 2 ^ 64 * 2 ^ 64 + β % 2 ^ 64
    have := Nat.div_add_mod β (2 ^ 64); omega
  have hγ_split : γ = γHi * 2 ^ 64 + γLo := by
    show γ = γ / 2 ^ 64 * 2 ^ 64 + γ % 2 ^ 64
    have := Nat.div_add_mod γ (2 ^ 64); omega
  -- Bounds.
  have hαLo_lt : αLo < 2 ^ 64 := Nat.mod_lt _ h64_pos
  have hβLo_lt : βLo < 2 ^ 64 := Nat.mod_lt _ h64_pos
  have hγLo_lt : γLo < 2 ^ 64 := Nat.mod_lt _ h64_pos
  have hαHi_lt : αHi < 2 ^ 60 := by
    show mU.toNat * gLo.toNat / 2 ^ 64 < 2 ^ 60
    rw [← hPLoHi]; exact hPLoHi_lt_60
  have hβHi_lt : βHi < 2 ^ 60 := by
    show mU.toNat * gMid.toNat / 2 ^ 64 < 2 ^ 60
    rw [← hPMidHi]; exact hPMidHi_lt_60
  have hγHi_lt : γHi < 2 ^ 60 := by
    show mU.toNat * gHi.toNat / 2 ^ 64 < 2 ^ 60
    rw [← hPHiHi]; exact hPHiHi_lt_60
  -- Component → UInt64 toNat equations.
  have hqLo_toNat : qLo.toNat = αLo := hPLoLo
  have hpLoHi_toNat : pLoHi.toNat = αHi := hPLoHi
  have hpMidLo_toNat : pMidLo.toNat = βLo := hPMidLo
  have hpMidHi_toNat : pMidHi.toNat = βHi := hPMidHi
  have hpHiLo_toNat : pHiLo.toNat = γLo := hPHiLo
  have hpHiHi_toNat : pHiHi.toNat = γHi := hPHiHi
  -- Layer 1: s1 = pLoHi + pMidLo (UInt64).
  -- s1.toNat = (αHi + βLo) mod 2^64.  c1 indicates carry (αHi + βLo ≥ 2^64).
  have hs1_carry : pLoHi.toNat + pMidLo.toNat
                    = s1.toNat + (if pLoHi.toNat + pMidLo.toNat < 2 ^ 64 then 0 else 2 ^ 64) :=
    UInt64_add_toNat_eq pLoHi pMidLo
  have hc1_eq : c1.toNat = (if pLoHi.toNat + pMidLo.toNat < 2 ^ 64 then 0 else 1) := by
    show (if s1 < pLoHi then (1 : UInt64) else 0).toNat = _
    by_cases hC : pLoHi.toNat + pMidLo.toNat < 2 ^ 64
    · have hNotLt : ¬ s1 < pLoHi := by rw [add_carry_iff]; omega
      simp only [hNotLt, if_false, if_pos hC]; decide
    · have hLt : s1 < pLoHi := by rw [add_carry_iff]; push_neg at hC; omega
      simp only [hLt, if_true, if_neg hC]; decide
  -- Layer 2a: s2a = pMidHi + pHiLo.
  have hs2a_carry : pMidHi.toNat + pHiLo.toNat
                    = s2a.toNat + (if pMidHi.toNat + pHiLo.toNat < 2 ^ 64 then 0 else 2 ^ 64) :=
    UInt64_add_toNat_eq pMidHi pHiLo
  have hc2a_eq : c2a.toNat = (if pMidHi.toNat + pHiLo.toNat < 2 ^ 64 then 0 else 1) := by
    show (if s2a < pMidHi then (1 : UInt64) else 0).toNat = _
    by_cases hC : pMidHi.toNat + pHiLo.toNat < 2 ^ 64
    · have hNotLt : ¬ s2a < pMidHi := by rw [add_carry_iff]; omega
      simp only [hNotLt, if_false, if_pos hC]; decide
    · have hLt : s2a < pMidHi := by rw [add_carry_iff]; push_neg at hC; omega
      simp only [hLt, if_true, if_neg hC]; decide
  -- Layer 2b: s2b = s2a + c1.
  have hs2b_carry : s2a.toNat + c1.toNat
                    = s2b.toNat + (if s2a.toNat + c1.toNat < 2 ^ 64 then 0 else 2 ^ 64) :=
    UInt64_add_toNat_eq s2a c1
  have hc2b_eq : c2b.toNat = (if s2a.toNat + c1.toNat < 2 ^ 64 then 0 else 1) := by
    show (if s2b < s2a then (1 : UInt64) else 0).toNat = _
    by_cases hC : s2a.toNat + c1.toNat < 2 ^ 64
    · have hNotLt : ¬ s2b < s2a := by rw [add_carry_iff]; omega
      simp only [hNotLt, if_false, if_pos hC]; decide
    · have hLt : s2b < s2a := by rw [add_carry_iff]; push_neg at hC; omega
      simp only [hLt, if_true, if_neg hC]; decide
  -- carryToHi.toNat = c2a.toNat + c2b.toNat (no overflow since each ≤ 1).
  -- c2a, c2b ∈ {0, 1}.
  have hc2a_le : c2a.toNat ≤ 1 := by rw [hc2a_eq]; split <;> omega
  have hc2b_le : c2b.toNat ≤ 1 := by rw [hc2b_eq]; split <;> omega
  have hc1_le : c1.toNat ≤ 1 := by rw [hc1_eq]; split <;> omega
  have hcTH_eq : carryToHi.toNat = c2a.toNat + c2b.toNat := by
    show (c2a + c2b).toNat = _
    rw [UInt64_add_toNat]
    apply Nat.mod_eq_of_lt
    have h64 : (2 : Nat) ^ 64 ≥ 4 := by decide
    omega
  -- qHi = pHiHi + carryToHi.  pHiHi.toNat < 2^60 and carryToHi.toNat ≤ 2 (no overflow).
  have hqHi_eq : qHi.toNat = pHiHi.toNat + carryToHi.toNat := by
    show (pHiHi + carryToHi).toNat = _
    rw [UInt64_add_toNat]
    apply Nat.mod_eq_of_lt
    have h60_lt_64 : (2 : Nat) ^ 60 < 2 ^ 64 := by decide
    have : pHiHi.toNat + carryToHi.toNat < 2 ^ 60 + 4 := by omega
    have : (2 : Nat) ^ 60 + 4 ≤ 2 ^ 64 := by decide
    omega
  -- Translate hs1_carry, hs2a_carry, hs2b_carry into Nat using component substitutions.
  have hs1_eq : αHi + βLo
                  = s1.toNat + (if αHi + βLo < 2 ^ 64 then 0 else 2 ^ 64) := by
    rw [← hpLoHi_toNat, ← hpMidLo_toNat]; exact hs1_carry
  have hc1_eq' : c1.toNat = (if αHi + βLo < 2 ^ 64 then 0 else 1) := by
    rw [← hpLoHi_toNat, ← hpMidLo_toNat]; exact hc1_eq
  have hs2a_eq : βHi + γLo
                  = s2a.toNat + (if βHi + γLo < 2 ^ 64 then 0 else 2 ^ 64) := by
    rw [← hpMidHi_toNat, ← hpHiLo_toNat]; exact hs2a_carry
  have hc2a_eq' : c2a.toNat = (if βHi + γLo < 2 ^ 64 then 0 else 1) := by
    rw [← hpMidHi_toNat, ← hpHiLo_toNat]; exact hc2a_eq
  -- The big arithmetic identity.  Target:
  --   quad256Nat qHi qMidHi qMidLo qLo
  --     = γHi·2^192 + γLo·2^128 + βHi·2^128 + βLo·2^64 + αHi·2^64 + αLo
  --     = m·(gHi·2^128 + gMid·2^64 + gLo).
  -- Strategy: express each q-limb in terms of (αHi, αLo, βHi, βLo, γHi, γLo)
  -- using the carry equations.
  have hα_full : α = αHi * 2 ^ 64 + αLo := hα_split
  have hβ_full : β = βHi * 2 ^ 64 + βLo := hβ_split
  have hγ_full : γ = γHi * 2 ^ 64 + γLo := hγ_split
  -- The full m·g expanded:
  have hMG_eq : mU.toNat * (gHi.toNat * 2 ^ 128 + gMid.toNat * 2 ^ 64 + gLo.toNat)
                  = γ * 2 ^ 128 + β * 2 ^ 64 + α := by
    show mU.toNat * (gHi.toNat * 2 ^ 128 + gMid.toNat * 2 ^ 64 + gLo.toNat) = _
    grind
  -- Goal: quad256Nat qHi qMidHi qMidLo qLo
  --        = (γHi · 2^64 + γLo) · 2^128 + (βHi · 2^64 + βLo) · 2^64 + (αHi · 2^64 + αLo)
  -- Drive everything to a quad256Nat in concrete UInt64 toNat form.
  show quad256Nat qHi qMidHi qMidLo qLo
        = mU.toNat * (gHi.toNat * 2 ^ 128 + gMid.toNat * 2 ^ 64 + gLo.toNat)
  rw [hMG_eq, hα_full, hβ_full, hγ_full]
  unfold quad256Nat
  rw [hqLo_toNat, hqHi_eq, hpHiHi_toNat, hcTH_eq]
  -- Introduce the cMid Nat-form carries.
  set cMid1 : Nat := if αHi + βLo < 2 ^ 64 then 0 else 2 ^ 64 with hcMid1_def
  set cMid2a : Nat := if βHi + γLo < 2 ^ 64 then 0 else 2 ^ 64 with hcMid2a_def
  set cMid2b : Nat := if s2a.toNat + c1.toNat < 2 ^ 64 then 0 else 2 ^ 64 with hcMid2b_def
  -- Linear identities (over Nat with subtraction-free formulations).
  have hs1_toNat_eq : s1.toNat + cMid1 = αHi + βLo := by
    rw [hcMid1_def]; exact hs1_eq.symm
  have hs2a_toNat_eq : s2a.toNat + cMid2a = βHi + γLo := by
    rw [hcMid2a_def]; exact hs2a_eq.symm
  have hs2b_toNat_eq : s2b.toNat + cMid2b = s2a.toNat + c1.toNat := by
    rw [hcMid2b_def]; exact hs2b_carry.symm
  -- Power-aligned carries: cMid1·2^64 = c1·2^128, etc.
  have hcMid1_pow : cMid1 * 2 ^ 64 = c1.toNat * 2 ^ 128 := by
    rw [hcMid1_def, hc1_eq']
    by_cases h : αHi + βLo < 2 ^ 64
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  have hcMid2a_pow : cMid2a * 2 ^ 128 = c2a.toNat * 2 ^ 192 := by
    rw [hcMid2a_def, hc2a_eq']
    by_cases h : βHi + γLo < 2 ^ 64
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  have hcMid2b_pow : cMid2b * 2 ^ 128 = c2b.toNat * 2 ^ 192 := by
    rw [hcMid2b_def, hc2b_eq]
    by_cases h : s2a.toNat + c1.toNat < 2 ^ 64
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  -- qMidLo = s1; qMidHi = s2b.
  have hqML_eq : qMidLo.toNat = s1.toNat := rfl
  have hqMH_eq : qMidHi.toNat = s2b.toNat := rfl
  rw [hqML_eq, hqMH_eq]
  -- Now the goal involves s2b.toNat · 2^128, s1.toNat · 2^64, etc.
  -- Build the master linear equation by multiplying the toNat equations:
  --   (s1.toNat + cMid1) · 2^64 = (αHi + βLo) · 2^64
  --   (s2a.toNat + cMid2a) · 2^128 = (βHi + γLo) · 2^128
  --   (s2b.toNat + cMid2b) · 2^128 = (s2a.toNat + c1.toNat) · 2^128
  have eq1 : (s1.toNat + cMid1) * 2 ^ 64 = (αHi + βLo) * 2 ^ 64 := by
    rw [hs1_toNat_eq]
  have eq2 : (s2a.toNat + cMid2a) * 2 ^ 128 = (βHi + γLo) * 2 ^ 128 := by
    rw [hs2a_toNat_eq]
  have eq3 : (s2b.toNat + cMid2b) * 2 ^ 128 = (s2a.toNat + c1.toNat) * 2 ^ 128 := by
    rw [hs2b_toNat_eq]
  -- Expand eq2, eq3 using grind distribution, then chain.
  have eq2' : s2a.toNat * 2 ^ 128 + cMid2a * 2 ^ 128 = βHi * 2 ^ 128 + γLo * 2 ^ 128 := by
    have h1 : (s2a.toNat + cMid2a) * 2 ^ 128 = s2a.toNat * 2 ^ 128 + cMid2a * 2 ^ 128 := by grind
    have h2 : (βHi + γLo) * 2 ^ 128 = βHi * 2 ^ 128 + γLo * 2 ^ 128 := by grind
    rw [h1] at eq2; rw [h2] at eq2; exact eq2
  have eq3' : s2b.toNat * 2 ^ 128 + cMid2b * 2 ^ 128
                = s2a.toNat * 2 ^ 128 + c1.toNat * 2 ^ 128 := by
    have h1 : (s2b.toNat + cMid2b) * 2 ^ 128 = s2b.toNat * 2 ^ 128 + cMid2b * 2 ^ 128 := by grind
    have h2 : (s2a.toNat + c1.toNat) * 2 ^ 128 = s2a.toNat * 2 ^ 128 + c1.toNat * 2 ^ 128 := by grind
    rw [h1] at eq3; rw [h2] at eq3; exact eq3
  have eq1' : s1.toNat * 2 ^ 64 + cMid1 * 2 ^ 64 = αHi * 2 ^ 64 + βLo * 2 ^ 64 := by
    have h1 : (s1.toNat + cMid1) * 2 ^ 64 = s1.toNat * 2 ^ 64 + cMid1 * 2 ^ 64 := by grind
    have h2 : (αHi + βLo) * 2 ^ 64 = αHi * 2 ^ 64 + βLo * 2 ^ 64 := by grind
    rw [h1] at eq1; rw [h2] at eq1; exact eq1
  -- Substitute power-aligned carries.
  rw [hcMid2a_pow] at eq2'
  rw [hcMid2b_pow] at eq3'
  rw [hcMid1_pow] at eq1'
  -- Now eq1' : s1.toNat · 2^64 + c1.toNat · 2^128 = αHi · 2^64 + βLo · 2^64
  --     eq2' : s2a.toNat · 2^128 + c2a.toNat · 2^192 = βHi · 2^128 + γLo · 2^128
  --     eq3' : s2b.toNat · 2^128 + c2b.toNat · 2^192 = s2a.toNat · 2^128 + c1.toNat · 2^128
  -- The goal is (after RHS distributed):
  --   (γHi + (c2a.toNat + c2b.toNat)) · 2^192 + s2b.toNat · 2^128 + s1.toNat · 2^64 + αLo
  --     = (γHi · 2^64 + γLo) · 2^128 + (βHi · 2^64 + βLo) · 2^64 + (αHi · 2^64 + αLo)
  -- Goal RHS: γHi·2^192 + γLo·2^128 + βHi·2^128 + βLo·2^64 + αHi·2^64 + αLo
  -- Subst (using eq3'): s2b·2^128 = s2a·2^128 + c1·2^128 - c2b·2^192.
  -- Subst (using eq2'): s2a·2^128 = βHi·2^128 + γLo·2^128 - c2a·2^192.
  -- Subst (using eq1'): s1·2^64 = αHi·2^64 + βLo·2^64 - c1·2^128.
  -- LHS = (γHi + c2a + c2b)·2^192 + βHi·2^128 + γLo·2^128 - c2a·2^192 + c1·2^128 - c2b·2^192
  --       + αHi·2^64 + βLo·2^64 - c1·2^128 + αLo
  --     = γHi·2^192 + βHi·2^128 + γLo·2^128 + αHi·2^64 + βLo·2^64 + αLo ✓
  -- omega closes given the three equalities.
  have hPow1 : (γHi * 2 ^ 64 + γLo) * 2 ^ 128 = γHi * 2 ^ 192 + γLo * 2 ^ 128 := by
    have : (γHi * 2 ^ 64) * 2 ^ 128 = γHi * 2 ^ 192 := by
      have : (γHi * 2 ^ 64) * 2 ^ 128 = γHi * (2 ^ 64 * 2 ^ 128) := by grind
      rw [this, show (2 : Nat) ^ 64 * 2 ^ 128 = 2 ^ 192 from by decide]
    grind
  have hPow2 : (βHi * 2 ^ 64 + βLo) * 2 ^ 64 = βHi * 2 ^ 128 + βLo * 2 ^ 64 := by
    have : (βHi * 2 ^ 64) * 2 ^ 64 = βHi * 2 ^ 128 := by
      have : (βHi * 2 ^ 64) * 2 ^ 64 = βHi * (2 ^ 64 * 2 ^ 64) := by grind
      rw [this, show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 from by decide]
    grind
  have hPow3 : (γHi + (c2a.toNat + c2b.toNat)) * 2 ^ 192
                = γHi * 2 ^ 192 + c2a.toNat * 2 ^ 192 + c2b.toNat * 2 ^ 192 := by grind
  rw [hPow1, hPow2, hPow3]
  -- Goal:
  --   γHi · 2^192 + c2a·2^192 + c2b·2^192 + s2b·2^128 + s1·2^64 + αLo
  --   = γHi · 2^192 + γLo · 2^128 + βHi · 2^128 + βLo · 2^64 + αHi · 2^64 + αLo
  -- With eq1', eq2', eq3' as linear equations, omega closes.
  grind

/-! ## 256-bit right-shift extraction

The kernel's right-shift branches must agree with
`quad256Nat / 2^shiftAmt`.  For binary64 inputs we have
`shiftAmt ∈ [188, 256)`, so only the two upper branches matter
(`s < 192` for `s ∈ [188, 192)`, `s ≥ 192` for `s ∈ [192, 256)`).

The 4-limb structure factors via `quad256Nat = qHi · 2^192 + triple192Nat`:
hence we can re-use `Kernel192.lean`'s 3-limb shift lemmas for the
triple part.
-/

/-- Decomposition: `quad256Nat = qHi · 2^192 + triple192Nat qMidHi qMidLo qLo`. -/
theorem quad256Nat_split (qHi qMidHi qMidLo qLo : UInt64) :
    quad256Nat qHi qMidHi qMidLo qLo
      = qHi.toNat * 2 ^ 192 + triple192Nat qMidHi qMidLo qLo := by
  unfold quad256Nat triple192Nat; grind

/-- Hi-branch (`s ∈ [192, 256)`): the kernel's `qHi >>> (s - 192)` equals
    `quad256Nat / 2^s.toNat`, provided `qHi.toNat < 2^(256 - s)`. -/
theorem shift_kernel256_hi_eq
    (qHi qMidHi qMidLo qLo : UInt64) (s s64 : UInt64)
    (hs_ge_192 : 192 ≤ s.toNat) (hs_lt_256 : s.toNat < 256)
    (hs64_def : s64 = s - 192) :
    (qHi >>> s64).toNat = quad256Nat qHi qMidHi qMidLo qLo / 2 ^ s.toNat := by
  have hs64_toNat : s64.toNat = s.toNat - 192 := by
    rw [hs64_def]
    apply UInt64_sub_toNat_of_ge s 192 (by decide) hs_ge_192
  have hs64_lt_64 : s64.toNat < 64 := by rw [hs64_toNat]; omega
  -- qHi >>> s64 = qHi.toNat / 2^s64.toNat.
  have hs64_inj : s64 = UInt64.ofNat s64.toNat := by
    rw [← UInt64.toNat_inj]
    rw [show (UInt64.ofNat s64.toNat).toNat = s64.toNat by
      apply UInt64.toNat_ofNat_of_lt'
      show s64.toNat < UInt64.size
      have h264 : UInt64.size = 2 ^ 64 := rfl
      rw [h264]; omega]
  have hqHi_shr : (qHi >>> s64).toNat = qHi.toNat / 2 ^ s64.toNat := by
    conv => lhs; rw [hs64_inj]
    exact UInt64_shr_toNat_lt qHi s64.toNat hs64_lt_64
  rw [hqHi_shr, hs64_toNat]
  rw [quad256Nat_split]
  -- (qHi · 2^192 + triple) / 2^s = qHi / 2^(s-192)  (when triple < 2^192 ≤ 2^s).
  have hTriple_lt : triple192Nat qMidHi qMidLo qLo < 2 ^ 192 := triple192Nat_lt _ _ _
  have hs_eq : 2 ^ s.toNat = 2 ^ 192 * 2 ^ (s.toNat - 192) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hs_eq, ← Nat.div_div_eq_div_mul]
  -- Goal: qHi.toNat / 2^(s-192) = ((qHi · 2^192 + triple) / 2^192) / 2^(s-192)
  rw [show qHi.toNat * 2 ^ 192 + triple192Nat qMidHi qMidLo qLo
        = triple192Nat qMidHi qMidLo qLo + qHi.toNat * 2 ^ 192 from by grind]
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 192)]
  rw [Nat.div_eq_of_lt hTriple_lt, Nat.zero_add]

/-- Mid-branch (`s ∈ [128, 192)`): for our use `s ∈ [188, 192)` so `s - 128 ∈ [60, 64)`.
    The kernel computes `(qMidHi >>> s64) ||| (qHi <<< (64 - s64))` where `s64 = s - 128`.
    This equals `quad256Nat / 2^s.toNat` provided `qHi < 2^s64`.

    Strategy: apply `shift_kernel_extract_mid` on the 3-limb subview
    `triple192Nat qHi qMidHi qLo` shifted by `sLift = s - 64 ∈ [64, 128)`.
    The kernel formula matches that lemma's output exactly.  Then show
    `triple192Nat qHi qMidHi qLo / 2^(s-64) = quad256Nat qHi qMidHi qMidLo qLo / 2^s`
    by factoring out 2^64 from both sides. -/
theorem shift_kernel256_mid_eq
    (qHi qMidHi qMidLo qLo : UInt64) (s s64 : UInt64)
    (hs_ge_128 : 128 ≤ s.toNat) (hs_lt_192 : s.toNat < 192)
    (hs64_def : s64 = s - 128)
    (hs64_nz : s64 ≠ 0)
    (hqHi_lt : qHi.toNat < 2 ^ s64.toNat) :
    ((qMidHi >>> s64) ||| (qHi <<< (64 - s64))).toNat
      = quad256Nat qHi qMidHi qMidLo qLo / 2 ^ s.toNat := by
  have hs64_toNat : s64.toNat = s.toNat - 128 := by
    rw [hs64_def]
    apply UInt64_sub_toNat_of_ge s 128 (by decide) hs_ge_128
  -- sLift = s - 64, in UInt64.
  set sLift : UInt64 := s - 64 with hsLift_def
  have hsLift_toNat : sLift.toNat = s.toNat - 64 := by
    rw [hsLift_def]
    apply UInt64_sub_toNat_of_ge s 64 (by decide); omega
  have hsLift_ge_64 : 64 ≤ sLift.toNat := by rw [hsLift_toNat]; omega
  have hsLift_lt_128 : sLift.toNat < 128 := by rw [hsLift_toNat]; omega
  -- s64 = sLift - 64 (UInt64).
  have hs64_alt : s64 = sLift - 64 := by
    rw [← UInt64.toNat_inj]
    rw [hs64_toNat]
    have hRHS : (sLift - 64).toNat = sLift.toNat - 64 := by
      apply UInt64_sub_toNat_of_ge sLift 64 (by decide) (by omega)
    rw [hRHS, hsLift_toNat]; omega
  -- Apply shift_kernel_extract_mid with (rHi = qHi, rMid = qMidHi, rLo = qLo), s := sLift, s64 = s64.
  have hExtract :
      ((qMidHi >>> s64) ||| (qHi <<< (64 - s64))).toNat
        = triple192Nat qHi qMidHi qLo / 2 ^ sLift.toNat :=
    shift_kernel_extract_mid qHi qMidHi qLo sLift s64
      hsLift_ge_64 hsLift_lt_128 hs64_alt hs64_nz hqHi_lt
  rw [hExtract]
  -- Now show: triple192Nat qHi qMidHi qLo / 2^(s-64) = quad256Nat qHi qMidHi qMidLo qLo / 2^s.
  -- Both equal `(qHi · 2^64 + qMidHi) / 2^(s-128)`.  Proof: factor 2^64 out of each.
  unfold quad256Nat triple192Nat
  -- LHS: (qHi · 2^128 + qMidHi · 2^64 + qLo) / 2^sLift, where qLo < 2^64.
  -- RHS: (qHi · 2^192 + qMidHi · 2^128 + qMidLo · 2^64 + qLo) / 2^s,
  --      where qMidLo · 2^64 + qLo < 2^128.
  -- Write 2^s = 2^(s-64) · 2^64 = 2^sLift · 2^64 (after substitution).
  have hPow_s : 2 ^ s.toNat = 2 ^ sLift.toNat * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; rw [hsLift_toNat]; omega
  -- Write 2^sLift = 2^s64' · 2^64 where s64' = sLift - 64.  We won't need this.
  -- Strategy: divide both sides of the goal by `* 2^64` via Nat.div_div.
  -- triple / 2^sLift = (qHi·2^128 + qMidHi·2^64 + qLo) / 2^sLift
  --                  = ((qHi·2^128 + qMidHi·2^64 + qLo) / 2^64) / 2^(sLift - 64)
  -- Hmm; we instead want to show LHS = RHS by computing both / 2^sLift directly.
  -- Even simpler: rewrite RHS as factoring out 2^64 from numerator and 2^sLift · 2^64 from denominator.
  -- RHS = quad / 2^s = quad / (2^sLift · 2^64) = (quad / 2^64) / 2^sLift.
  -- quad / 2^64 = qHi·2^128 + qMidHi·2^64 + qMidLo + (qLo / 2^64) = qHi·2^128 + qMidHi·2^64 + qMidLo.
  -- And LHS = (qHi·2^128 + qMidHi·2^64 + qLo) / 2^sLift.  But qMidLo and qLo are different.
  -- However: we're dividing by 2^sLift ≥ 2^64.  In both cases, the low qXX·1 is irrelevant
  -- as long as it's < 2^sLift.  Indeed qLo < 2^64 ≤ 2^sLift and qMidLo < 2^64 ≤ 2^sLift.
  --
  -- Cleaner: use that the only relevant bits for / 2^sLift are bits at positions ≥ sLift,
  -- which only depend on qHi, qMidHi (since sLift ≥ 64).
  rw [hPow_s]
  rw [show (2 ^ sLift.toNat * 2 ^ 64 : Nat) = 2 ^ 64 * 2 ^ sLift.toNat by grind]
  rw [← Nat.div_div_eq_div_mul]
  -- LHS: (qHi · 2^128 + qMidHi · 2^64 + qLo) / 2^sLift.toNat
  -- RHS: (qHi · 2^192 + qMidHi · 2^128 + qMidLo · 2^64 + qLo) / 2^64 / 2^sLift.toNat
  -- Compute the inner division for RHS.
  have hQLo_lt : qLo.toNat < 2 ^ 64 := qLo.toNat_lt
  have hRearr_inner :
      qHi.toNat * 2 ^ 192 + qMidHi.toNat * 2 ^ 128 + qMidLo.toNat * 2 ^ 64 + qLo.toNat
        = qLo.toNat
            + (qHi.toNat * 2 ^ 128 + qMidHi.toNat * 2 ^ 64 + qMidLo.toNat) * 2 ^ 64 := by
    have h128_64 : (2 : Nat) ^ 128 * 2 ^ 64 = 2 ^ 192 := by decide
    have h64_64 : (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 := by decide
    have : (qHi.toNat * 2 ^ 128 + qMidHi.toNat * 2 ^ 64 + qMidLo.toNat) * 2 ^ 64
            = qHi.toNat * (2 ^ 128 * 2 ^ 64) + qMidHi.toNat * (2 ^ 64 * 2 ^ 64)
                + qMidLo.toNat * 2 ^ 64 := by grind
    rw [this, h128_64, h64_64]; grind
  rw [hRearr_inner]
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64)]
  rw [Nat.div_eq_of_lt hQLo_lt, Nat.zero_add]
  -- LHS: (qHi · 2^128 + qMidHi · 2^64 + qLo) / 2^sLift.toNat
  -- RHS: (qHi · 2^128 + qMidHi · 2^64 + qMidLo) / 2^sLift.toNat
  -- These have qLo vs qMidLo at the bottom.  Both are < 2^64 ≤ 2^sLift, hence equal
  -- modulo 2^sLift?  No — the division by 2^sLift collapses the low 64 bits to 0
  -- if the upper parts are larger.  Specifically:
  -- (M · 2^64 + x) / 2^sLift, where sLift ∈ [64, 128) and x < 2^64.
  -- = (M · 2^64 + x) / (2^64 · 2^(sLift - 64))
  -- = ((M · 2^64 + x) / 2^64) / 2^(sLift - 64)
  -- = (M + x / 2^64) / 2^(sLift - 64)
  -- = M / 2^(sLift - 64)   (since x < 2^64).
  -- The result depends only on M.  And M is the same in LHS (qHi · 2^64 + qMidHi)
  -- as in RHS (qHi · 2^64 + qMidHi).  ✓
  set M : Nat := qHi.toNat * 2 ^ 64 + qMidHi.toNat with hM_def
  have hLHS_eq :
      qHi.toNat * 2 ^ 128 + qMidHi.toNat * 2 ^ 64 + qLo.toNat
        = qLo.toNat + M * 2 ^ 64 := by
    rw [hM_def]
    have h128_64 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
    rw [h128_64]; grind
  have hRHS_eq :
      qHi.toNat * 2 ^ 128 + qMidHi.toNat * 2 ^ 64 + qMidLo.toNat
        = qMidLo.toNat + M * 2 ^ 64 := by
    rw [hM_def]
    have h128_64 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by decide
    rw [h128_64]; grind
  rw [hLHS_eq, hRHS_eq]
  -- Now: (qLo + M · 2^64) / 2^sLift = (qMidLo + M · 2^64) / 2^sLift.
  -- 2^sLift = 2^64 · 2^(sLift - 64).  Divide twice.
  have hPow_sLift : 2 ^ sLift.toNat = 2 ^ 64 * 2 ^ (sLift.toNat - 64) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hPow_sLift]
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64)]
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64)]
  have hQMidLo_lt : qMidLo.toNat < 2 ^ 64 := qMidLo.toNat_lt
  rw [Nat.div_eq_of_lt hQLo_lt, Nat.div_eq_of_lt hQMidLo_lt]

/-! ## 192-bit precision sandwich and slack bounds

These mirror `shiftedSig_sandwich` and `shiftedSig_slack_bound` from
`KernelCorrectness.lean`, but for the 192-bit table with `g ≥ 2^191`.
-/

/-- 192-bit slack bound: `m · B · 2^190 ≤ N · 2^s` from `g ≥ 2^191`. -/
theorem shiftedSig_slack_bound_192
    (m g qPos qNeg kPos kNeg hPos hNeg s : Nat)
    (hg : 2 ^ 191 ≤ g)
    (hRegroup : 2 ^ s * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos)
    (hInv : 10 ^ kNeg * 2 ^ hPos ≤ g * 10 ^ kPos * 2 ^ hNeg
              ∧ g * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg) :
    m * (2 ^ qNeg * 10 ^ kPos) * 2 ^ 190
      ≤ m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s := by
  -- Mirror of `shiftedSig_slack_bound` with the wider precision factor 2^190.
  -- Step 1: 2^190 · 10^kPos · 2^hNeg ≤ 10^kNeg · 2^hPos (table high-precision bound at 191).
  obtain ⟨_, hHi⟩ := hInv
  -- From `g ≥ 2^191`: (2^191) · 10^kPos · 2^hNeg ≤ g · 10^kPos · 2^hNeg < 10^kNeg · 2^hPos + 10^kPos · 2^hNeg.
  -- Hence (2^191 - 1) · 10^kPos · 2^hNeg < 10^kNeg · 2^hPos.  Then 2^190 ≤ 2^191 - 1.
  have h1 : 2 ^ 191 * (10 ^ kPos * 2 ^ hNeg) ≤ g * 10 ^ kPos * 2 ^ hNeg := by
    have := Nat.mul_le_mul_right (10 ^ kPos * 2 ^ hNeg) hg
    have hrw2 : g * (10 ^ kPos * 2 ^ hNeg) = g * 10 ^ kPos * 2 ^ hNeg := by grind
    rw [hrw2] at this; exact this
  have h2 : 2 ^ 191 * (10 ^ kPos * 2 ^ hNeg) < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg :=
    Nat.lt_of_le_of_lt h1 hHi
  have hExpand : (2 ^ 191 - 1) * (10 ^ kPos * 2 ^ hNeg)
                  = 2 ^ 191 * (10 ^ kPos * 2 ^ hNeg) - 10 ^ kPos * 2 ^ hNeg := by
    have := Nat.sub_mul (2 ^ 191) 1 (10 ^ kPos * 2 ^ hNeg); omega
  have h2_191_pos : (1 : Nat) ≤ 2 ^ 191 := Nat.one_le_two_pow
  have hStrict : (2 ^ 191 - 1) * (10 ^ kPos * 2 ^ hNeg) < 10 ^ kNeg * 2 ^ hPos := by omega
  -- 2^190 ≤ 2^191 - 1.
  have h190_le : 2 ^ 190 ≤ 2 ^ 191 - 1 := by
    have : (2 : Nat) ^ 191 = 2 * 2 ^ 190 := by
      rw [show (191 : Nat) = 1 + 190 from rfl, Nat.pow_add, Nat.pow_one]
    have h1 : 1 ≤ 2 ^ 190 := Nat.one_le_two_pow
    omega
  have hWeak : 2 ^ 190 * (10 ^ kPos * 2 ^ hNeg) ≤ 10 ^ kNeg * 2 ^ hPos := by
    have h_le : 2 ^ 190 * (10 ^ kPos * 2 ^ hNeg) ≤ (2 ^ 191 - 1) * (10 ^ kPos * 2 ^ hNeg) :=
      Nat.mul_le_mul_right _ h190_le
    omega
  -- Multiply through by m · 2^qNeg, apply regroup.
  have hMul : m * 2 ^ qNeg * (2 ^ 190 * (10 ^ kPos * 2 ^ hNeg))
                ≤ m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos) :=
    Nat.mul_le_mul_left _ hWeak
  have hLHS_eq : m * 2 ^ qNeg * (2 ^ 190 * (10 ^ kPos * 2 ^ hNeg))
                  = m * (2 ^ qNeg * 10 ^ kPos) * 2 ^ 190 * 2 ^ hNeg := by grind
  have hRHS_eq : m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos)
                  = m * 2 ^ qPos * 10 ^ kNeg * 2 ^ s * 2 ^ hNeg := by
    have hMul' : m * 2 ^ qNeg * (10 ^ kNeg * 2 ^ hPos)
                  = m * 10 ^ kNeg * (2 ^ qNeg * 2 ^ hPos) := by grind
    rw [hMul', ← hRegroup]; grind
  rw [hLHS_eq, hRHS_eq] at hMul
  exact Nat.le_of_mul_le_mul_right hMul (Nat.two_pow_pos _)

/-! ## Bridge: `shiftedSig_v4` agrees with `shiftedSig`

The proof structure mirrors `shiftedSig_eq_fast2`:
- Stage 1: when any guard fails (m ≥ 2^60, k out of table range,
  shiftAmt out of [188, 256), or B ≥ 2^128), fall through to spec.
- Stage 2: in the safe regime, apply `shiftedSig_floor_safe`.
-/

/-- Guard-fallback for `shiftedSig_v4`: when any width guard fails, or the
    binary64-domain predicate `0<m<2^53 ∧ -1074≤q≤971 ∧ k = kOfMQ m q`
    fails, `shiftedSig_v4 m q k = shiftedSig m q k`. -/
theorem shiftedSig_v4_guards
    (m : Nat) (q k : Int)
    (hGuard : m ≥ (1 <<< 60 : Nat) ∨
              -k < pow10Table192_kMin ∨ -k > pow10Table192_kMax ∨
              ((pow10Lookup192 (-k)).2.2.2 - q) < 188 ∨
              ((pow10Lookup192 (-k)).2.2.2 - q) ≥ 256 ∨
              ¬(0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q)) :
    shiftedSig_v4 m q k = shiftedSig m q k := by
  unfold shiftedSig_v4
  rcases hGuard with h | h | h | h | h | h
  · simp only [dif_pos h]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [dif_pos h1]
    · simp only [dif_neg h1, dif_pos h]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [dif_pos h1]
    · by_cases h2 : (-k : Int) < pow10Table192_kMin
      · simp only [dif_neg h1, dif_pos h2]
      · simp only [dif_neg h1, dif_neg h2, dif_pos h]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [dif_pos h1]
    · by_cases h2 : (-k : Int) < pow10Table192_kMin
      · simp only [dif_neg h1, dif_pos h2]
      · by_cases h3 : (-k : Int) > pow10Table192_kMax
        · simp only [dif_neg h1, dif_neg h2, dif_pos h3]
        · simp only [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [dif_pos h1]
    · by_cases h2 : (-k : Int) < pow10Table192_kMin
      · simp only [dif_neg h1, dif_pos h2]
      · by_cases h3 : (-k : Int) > pow10Table192_kMax
        · simp only [dif_neg h1, dif_neg h2, dif_pos h3]
        · by_cases h4 : ((pow10Lookup192 (-k)).2.2.2 - q) < 188
          · simp only [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
          · simp only [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_pos h]
  · by_cases h1 : m ≥ (1 <<< 60 : Nat)
    · simp only [dif_pos h1]
    · by_cases h2 : (-k : Int) < pow10Table192_kMin
      · simp only [dif_neg h1, dif_pos h2]
      · by_cases h3 : (-k : Int) > pow10Table192_kMax
        · simp only [dif_neg h1, dif_neg h2, dif_pos h3]
        · by_cases h4 : ((pow10Lookup192 (-k)).2.2.2 - q) < 188
          · simp only [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
          · by_cases h5 : ((pow10Lookup192 (-k)).2.2.2 - q) ≥ 256
            · simp only [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_pos h5]
            · -- Final case: h is the binary64-domain predicate's negation.
              simp only [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5,
                          dif_neg h]

/-! ## R20-widened core: `shiftedSig m q k = (m · g192) / 2^shiftAmt`

When the width guards pass and `(m, q)` is binary64 with `k = kOfMQ m q`,
the spec `shiftedSig` simplifies to the multiply-shift floor `(m · g) / 2^s`
— with NO `B < 2^k` accuracy guard, via the unconditional R20 residue.
This is the 192-bit analog of `shiftedSig_fast2_w_eq_binary64`. -/

set_option maxRecDepth 8000 in
/-- **R20-widened 192-bit core.**  For every binary64 `(m, q)`
    (`0 < m < 2^53`, `-1074 ≤ q ≤ 971`) with `k = kOfMQ m q` and all width
    guards passing, the spec `shiftedSig` equals the 192-bit multiply-shift
    floor — with NO `B < 2^k` accuracy guard.  The closing step feeds the
    unconditional R20 residue (`residueR20Cond_decode_binary64`) through
    `shiftedSig_floor_of_residue`, mirroring `shiftedSig_fast2_w_eq_binary64`
    in the 128-bit case. -/
theorem shiftedSig_v4_eq_widened_core
    (m : Nat) (q k : Int)
    (hm : 0 < m) (hm53 : m < 2 ^ 53)
    (hq_lo : -1074 ≤ q) (hq_hi : q ≤ 971) (hk : k = kOfMQ m q)
    (hm_lt_60 : m < 2 ^ 60)
    (hkLo : pow10Table192_kMin ≤ -k) (hkHi : -k ≤ pow10Table192_kMax)
    (hsLo : 188 ≤ (pow10Lookup192 (-k)).2.2.2 - q)
    (hsHi : (pow10Lookup192 (-k)).2.2.2 - q < 256)
    (gHi gMid gLo : UInt64) (h_t shiftAmt : Int)
    (hgHi_def : gHi = (pow10Lookup192 (-k)).1)
    (hgMid_def : gMid = (pow10Lookup192 (-k)).2.1)
    (hgLo_def : gLo = (pow10Lookup192 (-k)).2.2.1)
    (hh_def : h_t = (pow10Lookup192 (-k)).2.2.2)
    (hshiftAmt_def : shiftAmt = h_t - q) :
    shiftedSig m q k
      = m * (gHi.toNat * 2 ^ 128 + gMid.toNat * 2 ^ 64 + gLo.toNat) / 2 ^ shiftAmt.toNat := by
  -- m = 0 case: trivial.
  by_cases hm0 : m = 0
  · subst hm0; unfold shiftedSig; simp
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
  set hPos : Nat := if h_t ≥ 0 then h_t.toNat else 0 with hhPos_def
  set hNeg : Nat := if h_t < 0 then (-h_t).toNat else 0 with hhNeg_def
  set G : Nat := gHi.toNat * 2 ^ 128 + gMid.toNat * 2 ^ 64 + gLo.toNat with hG_def
  set B : Nat := 2 ^ qNeg * 10 ^ kPos with hB_def
  set N : Nat := m * 2 ^ qPos * 10 ^ kNeg with hN_def
  -- B > 0.
  have hB_pos : 0 < B := by
    rw [hB_def]; exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by decide))
  -- shiftAmt = h_t - q ∈ [188, 256).
  have hshiftAmt_nn : 0 ≤ shiftAmt := by rw [hshiftAmt_def]; omega
  have hshiftAmt_lo : 188 ≤ shiftAmt := by rw [hshiftAmt_def]; omega
  have hshiftAmt_hi : shiftAmt < 256 := by rw [hshiftAmt_def]; omega
  have hshiftAmt_toNat_lo : 188 ≤ shiftAmt.toNat := by
    have := Int.toNat_of_nonneg hshiftAmt_nn; omega
  -- Power regrouping: 2^shiftAmt.toNat · 2^qPos · 2^hNeg = 2^qNeg · 2^hPos.
  have hregroup_eq : shiftAmt.toNat + qPos + hNeg = qNeg + hPos := by
    have hShiftAmt_int : (shiftAmt.toNat : Int) = shiftAmt := Int.toNat_of_nonneg hshiftAmt_nn
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
        have hh_nn : 0 ≤ h_t := by
          have h1 : 188 ≤ h_t - q := by rw [hh_def]; exact hsLo
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
    have hL : ((shiftAmt.toNat + qPos + hNeg : Nat) : Int)
                = ((qNeg + hPos : Nat) : Int) := by push_cast; omega
    exact_mod_cast hL
  have hRegroup : 2 ^ shiftAmt.toNat * 2 ^ qPos * 2 ^ hNeg = 2 ^ qNeg * 2 ^ hPos :=
    two_pow_regroup shiftAmt.toNat qNeg qPos hPos hNeg
      (by have := hregroup_eq; omega)
  -- Table invariant: G satisfies the ceiling bound.
  have hInv := pow10Lookup192_invariant (-k) hkLo hkHi
  -- Translate keys.
  have hkPos'_eq_kNeg : (if (-k : Int) ≥ 0 then (-k).toNat else 0) = kNeg := by
    rw [hkNeg_def]
    by_cases hk_nn : k ≥ 0
    · by_cases hk_pos : k = 0
      · subst hk_pos; simp
      · have hk_pos' : k > 0 := (by omega)
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
      · have hk_pos : k > 0 := (by omega)
        have h_neg_k_lt : (-k : Int) < 0 := by omega
        have hk_nn' : k ≥ 0 := hk_nn
        rw [if_pos h_neg_k_lt, if_pos hk_nn']
        have : -(-k) = k := by grind
        rw [this]
    · push_neg at hk_nn
      have h_neg_k_nn : ¬ (-k : Int) < 0 := by omega
      have hk_nn_not : ¬ k ≥ 0 := by omega
      rw [if_neg h_neg_k_nn, if_neg hk_nn_not]
  have hh_t_eq : (pow10Lookup192 (-k)).2.2.2 = h_t := by rw [← hh_def]
  have hG_eq : (pow10Lookup192 (-k)).1.toNat * 2 ^ 128
                + (pow10Lookup192 (-k)).2.1.toNat * 2 ^ 64
                + (pow10Lookup192 (-k)).2.2.1.toNat = G := by
    rw [hG_def, ← hgHi_def, ← hgMid_def, ← hgLo_def]
  have hInv' : 10 ^ kNeg * 2 ^ hPos ≤ G * 10 ^ kPos * 2 ^ hNeg
              ∧ G * 10 ^ kPos * 2 ^ hNeg < 10 ^ kNeg * 2 ^ hPos + 10 ^ kPos * 2 ^ hNeg := by
    have h1 := hInv
    simp only at h1
    have hkPos'_eq := hkPos'_eq_kNeg
    have hkNeg'_eq := hkNeg'_eq_kPos
    have hhPos'_eq : (if (pow10Lookup192 (-k)).2.2.2 ≥ 0 then
                        ((pow10Lookup192 (-k)).2.2.2).toNat else 0) = hPos := by
      rw [hhPos_def, hh_t_eq]
    have hhNeg'_eq : (if (pow10Lookup192 (-k)).2.2.2 < 0 then
                        (-(pow10Lookup192 (-k)).2.2.2).toNat else 0) = hNeg := by
      rw [hhNeg_def, hh_t_eq]
    rw [hkPos'_eq, hkNeg'_eq, hhPos'_eq, hhNeg'_eq, hG_eq] at h1
    exact h1
  -- Apply shiftedSig_sandwich.
  have hSandwich := shiftedSig_sandwich m G qPos qNeg kPos kNeg hPos hNeg shiftAmt.toNat
                      hm_pos hRegroup hInv'
  -- R20 residue (the widened input, no `B < 2^k`).  Valid for any
  -- `shiftAmt.toNat ≥ 124`; here `shiftAmt.toNat ≥ 188`.
  have hResidue : residueR20Cond m B shiftAmt.toNat N := by
    have hr := residueR20Cond_decode_binary64 m q shiftAmt.toNat hm hm53 hq_lo hq_hi
                 (by omega)
    rw [← hk] at hr
    -- Rewrite hr (keyed by the same sign-splits) to B, N.
    rw [hB_def, hN_def, hqNeg_def, hkPos_def, hqPos_def, hkNeg_def]
    first
    | exact hr
    | grind
  -- Floor equality via the widened (residue-based) closing step.
  have hFloor := shiftedSig_floor_of_residue m G B shiftAmt.toNat N hB_pos hSandwich hResidue
  exact hFloor.symm

/-! ## Main bridge: `shiftedSig_v4 m q k = shiftedSig m q k`

`shiftedSig_v4` takes the 192-bit kernel when the width guards pass and
`(m, q)` is binary64 with `k = kOfMQ m q`; otherwise it falls back to the
spec.  On the kernel branch the floor equality holds unconditionally
(no `B < 2^k` accuracy guard) via the R20 residue
(`shiftedSig_v4_eq_widened_core`).  For real binary64 decodes the kernel
branch is always taken, so the spec/GMP fallback is unreachable on the
hot path. -/

set_option maxRecDepth 8000 in
theorem shiftedSig_v4_eq (m : Nat) (q k : Int) :
    shiftedSig_v4 m q k = shiftedSig m q k := by
  -- Stage 1: dispatch all guard branches to spec.
  by_cases hm60 : m ≥ (1 <<< 60 : Nat)
  · exact shiftedSig_v4_guards m q k (Or.inl hm60)
  by_cases hk : (-k : Int) < pow10Table192_kMin ∨ (-k : Int) > pow10Table192_kMax
  · rcases hk with h | h
    · exact shiftedSig_v4_guards m q k (Or.inr (Or.inl h))
    · exact shiftedSig_v4_guards m q k (Or.inr (Or.inr (Or.inl h)))
  by_cases hs : (pow10Lookup192 (-k)).2.2.2 - q < 188 ∨
                 (pow10Lookup192 (-k)).2.2.2 - q ≥ 256
  · rcases hs with h | h
    · exact shiftedSig_v4_guards m q k
              (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact shiftedSig_v4_guards m q k
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  by_cases hDom : ¬(0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q)
  · exact shiftedSig_v4_guards m q k
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hDom)))))
  -- Stage 2: all width guards passed and the binary64-domain predicate holds.
  push_neg at hm60 hk hs
  rw [Decidable.not_not] at hDom
  obtain ⟨hkLo, hkHi⟩ := hk
  obtain ⟨hsLo, hsHi⟩ := hs
  obtain ⟨hm_dom, hm53_dom, hq_lo_dom, hq_hi_dom, hk_dom⟩ := hDom
  -- Unfold v4.
  unfold shiftedSig_v4
  have hm60_not : ¬ m ≥ (1 <<< 60 : Nat) := by omega
  rw [dif_neg hm60_not]
  have hk_lo_not : ¬ ((-k : Int) < pow10Table192_kMin) := by omega
  have hk_hi_not : ¬ ((-k : Int) > pow10Table192_kMax) := by omega
  rw [dif_neg hk_lo_not, dif_neg hk_hi_not]
  have hs_lo_not : ¬ ((pow10Lookup192 (-k)).2.2.2 - q < 188) := by omega
  have hs_hi_not : ¬ ((pow10Lookup192 (-k)).2.2.2 - q ≥ 256) := by omega
  rw [dif_neg hs_lo_not, dif_neg hs_hi_not]
  have hDom_pred : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q :=
    ⟨hm_dom, hm53_dom, hq_lo_dom, hq_hi_dom, hk_dom⟩
  rw [dif_pos hDom_pred]
  -- Introduce kernel intermediates.
  set gHi : UInt64 := (pow10Lookup192 (-k)).1 with hgHi_def
  set gMid : UInt64 := (pow10Lookup192 (-k)).2.1 with hgMid_def
  set gLo : UInt64 := (pow10Lookup192 (-k)).2.2.1 with hgLo_def
  set h_t : Int := (pow10Lookup192 (-k)).2.2.2 with hh_def
  set shiftAmt : Int := h_t - q with hshiftAmt_def
  set mU : UInt64 := UInt64.ofNat m with hmU_def
  set sU : UInt64 := UInt64.ofNat shiftAmt.toNat with hsU_def
  -- Bounds.
  have hshiftAmt_nn : 0 ≤ shiftAmt := by rw [hshiftAmt_def]; omega
  have hshiftAmt_lo : 188 ≤ shiftAmt := by rw [hshiftAmt_def]; omega
  have hshiftAmt_hi : shiftAmt < 256 := by rw [hshiftAmt_def]; omega
  have hshiftAmt_toNat_lo : 188 ≤ shiftAmt.toNat := by
    have := Int.toNat_of_nonneg hshiftAmt_nn; omega
  have hshiftAmt_toNat_hi : shiftAmt.toNat < 256 := by
    have := Int.toNat_of_nonneg hshiftAmt_nn; omega
  have hshiftAmt_lt_2_64 : shiftAmt.toNat < 2 ^ 64 := by
    have h264 : (256 : Nat) < 2 ^ 64 := by decide
    omega
  have hsU_toNat : sU.toNat = shiftAmt.toNat :=
    UInt64_ofNat_toNat_of_lt _ hshiftAmt_lt_2_64
  -- m fits in UInt64.
  have hm_lt_60 : m < 2 ^ 60 := by
    have h : (1 <<< 60 : Nat) = 2 ^ 60 := by decide
    omega
  have hm_lt_64 : m < 2 ^ 64 := by
    have : (2 : Nat) ^ 60 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hmU_toNat : mU.toNat = m := UInt64_ofNat_toNat_of_lt _ hm_lt_64
  have hmU_lt_60 : mU.toNat < 2 ^ 60 := hmU_toNat.symm ▸ hm_lt_60
  -- Apply the kernel-mul correctness lemma to get the quad256 value.
  have hQuad := shiftedSig_u192_kernel_mul_eq mU gHi gMid gLo hmU_lt_60
  -- hQuad: quad256Nat (qHi, qMidHi, qMidLo, qLo) = mU.toNat * (gHi · 2^128 + gMid · 2^64 + gLo)
  -- with qHi, qMidHi, qMidLo, qLo as defined in the kernel.
  -- Unfold the kernel (LHS of the goal) to bind these.
  show (shiftedSig_u192_kernel mU gHi gMid gLo sU).toNat = shiftedSig m q k
  unfold shiftedSig_u192_kernel
  -- The shift branches.  shiftAmt ∈ [188, 256), so:
  --   sU < 64?  no  (sU.toNat ≥ 188)
  --   sU < 128? no  (sU.toNat ≥ 188)
  --   sU < 192? yes/no depending on actual value
  have hsU_ge_64 : ¬ sU < (64 : UInt64) := by
    rw [UInt64_lt_64_iff]; rw [hsU_toNat]; omega
  have hsU_ge_128 : ¬ sU < (128 : UInt64) := by
    rw [UInt64_lt_128_iff]; rw [hsU_toNat]; omega
  simp only [if_neg hsU_ge_64, if_neg hsU_ge_128]
  -- Bind the kernel-internal limbs.
  set pLoLo  : UInt64 := mU * gLo
  set pLoHi  : UInt64 := mulHi64 mU gLo
  set pMidLo : UInt64 := mU * gMid
  set pMidHi : UInt64 := mulHi64 mU gMid
  set pHiLo  : UInt64 := mU * gHi
  set pHiHi  : UInt64 := mulHi64 mU gHi
  set s1 : UInt64 := pLoHi + pMidLo
  set c1 : UInt64 := if s1 < pLoHi then (1 : UInt64) else 0
  set qMidLo : UInt64 := s1
  set s2a : UInt64 := pMidHi + pHiLo
  set c2a : UInt64 := if s2a < pMidHi then (1 : UInt64) else 0
  set s2b : UInt64 := s2a + c1
  set c2b : UInt64 := if s2b < s2a then (1 : UInt64) else 0
  set qMidHi : UInt64 := s2b
  set carryToHi : UInt64 := c2a + c2b
  set qHi : UInt64 := pHiHi + carryToHi
  set qLo : UInt64 := pLoLo
  -- Reorganise hQuad.  After all the `set` calls, the let-bindings inside `quad256Nat`
  -- should be syntactically identical.
  -- hQuad's let-introduced qHi, etc., match our set-introduced qHi, etc.
  -- Goal at this point:
  --   (if sU < 192 then ... else ...).toNat = shiftedSig m q k
  -- where the branches are the 192- and 256-bit shift formulas.
  -- shiftAmt.toNat ∈ [188, 256).  Case split on the 192 boundary.
  by_cases hsU_lt_192 : sU < (192 : UInt64)
  · -- Mid branch: s ∈ [188, 192).
    rw [if_pos hsU_lt_192]
    have hsU_toNat_lt_192 : sU.toNat < 192 := by
      have := (UInt64.lt_iff_toNat_lt (a := sU) (b := 192)).mp hsU_lt_192
      exact this
    have hshift_lt_192 : shiftAmt.toNat < 192 := by rw [← hsU_toNat]; exact hsU_toNat_lt_192
    -- Define s64 = sU - 128.
    set s64 : UInt64 := sU - 128
    have hs64_toNat : s64.toNat = sU.toNat - 128 := by
      apply UInt64_sub_toNat_of_ge sU 128 (by decide)
      rw [hsU_toNat]; omega
    have hs64_ge_60 : 60 ≤ s64.toNat := by rw [hs64_toNat, hsU_toNat]; omega
    have hs64_lt_64 : s64.toNat < 64 := by rw [hs64_toNat, hsU_toNat]; omega
    have hs64_nz : s64 ≠ 0 := by
      intro hz
      have : s64.toNat = 0 := by rw [hz]; rfl
      omega
    rw [if_neg hs64_nz]
    -- Bound qHi.toNat < 2^60 via kernel-mul correctness.  Then qHi < 2^s64 since s64 ≥ 60.
    have hG_lt_192 : gHi.toNat * 2 ^ 128 + gMid.toNat * 2 ^ 64 + gLo.toNat < 2 ^ 192 := by
      have hgH : gHi.toNat < 2 ^ 64 := gHi.toNat_lt
      have hgM : gMid.toNat < 2 ^ 64 := gMid.toNat_lt
      have hgL : gLo.toNat < 2 ^ 64 := gLo.toNat_lt
      have h1 : gHi.toNat * 2 ^ 128 ≤ (2 ^ 64 - 1) * 2 ^ 128 := by
        apply Nat.mul_le_mul_right; omega
      have h2 : gMid.toNat * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
        apply Nat.mul_le_mul_right; omega
      have hA : (2 ^ 64 - 1) * 2 ^ 128 = 2 ^ 64 * 2 ^ 128 - 2 ^ 128 := by
        rw [Nat.sub_mul]
      have hB : (2 ^ 64 - 1) * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 - 2 ^ 64 := by
        rw [Nat.sub_mul]
      have h64_128 : (2 : Nat) ^ 64 * 2 ^ 128 = 2 ^ 192 := by decide
      have h64_64 : (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 := by decide
      have h_128_le : (2 : Nat) ^ 128 ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by decide)
      have h_64_le : (2 : Nat) ^ 64 ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by decide)
      omega
    have hProd_lt_252 : mU.toNat * (gHi.toNat * 2 ^ 128 + gMid.toNat * 2 ^ 64 + gLo.toNat)
                          < 2 ^ 252 := by
      have h1 : mU.toNat * (gHi.toNat * 2 ^ 128 + gMid.toNat * 2 ^ 64 + gLo.toNat)
              < 2 ^ 60 * 2 ^ 192 := Nat.mul_lt_mul_of_lt_of_lt hmU_lt_60 hG_lt_192
      have h60_192 : (2 : Nat) ^ 60 * 2 ^ 192 = 2 ^ 252 := by decide
      omega
    have hQuad_lt_252 : quad256Nat qHi qMidHi qMidLo qLo < 2 ^ 252 := by
      rw [hQuad]; exact hProd_lt_252
    have hqHi_lt_60 : qHi.toNat < 2 ^ 60 := by
      have hQuad_ge : qHi.toNat * 2 ^ 192 ≤ quad256Nat qHi qMidHi qMidLo qLo := by
        unfold quad256Nat; omega
      have h_lt : qHi.toNat * 2 ^ 192 < 2 ^ 252 := by omega
      have h_pow : (2 : Nat) ^ 252 = 2 ^ 60 * 2 ^ 192 := by decide
      rw [h_pow] at h_lt
      exact Nat.lt_of_mul_lt_mul_right h_lt
    have hqHi_lt : qHi.toNat < 2 ^ s64.toNat := by
      have h60_le : (2 : Nat) ^ 60 ≤ 2 ^ s64.toNat :=
        Nat.pow_le_pow_right (by decide) hs64_ge_60
      omega
    -- Apply shift extraction.
    have hKernel_eq := shift_kernel256_mid_eq qHi qMidHi qMidLo qLo sU s64
              (by rw [hsU_toNat]; omega) hsU_toNat_lt_192 rfl hs64_nz hqHi_lt
    rw [hKernel_eq, hQuad]
    -- Goal: mU.toNat * (gHi · 2^128 + gMid · 2^64 + gLo) / 2 ^ sU.toNat = shiftedSig m q k
    rw [hmU_toNat, hsU_toNat]
    -- Now reduce shiftedSig m q k via the R20-widened core.
    exact (shiftedSig_v4_eq_widened_core m q k hm_dom hm53_dom hq_lo_dom hq_hi_dom hk_dom
            hm_lt_60 hkLo hkHi hsLo hsHi
            gHi gMid gLo h_t shiftAmt hgHi_def hgMid_def hgLo_def hh_def hshiftAmt_def).symm
  · -- Hi branch: s ∈ [192, 256).
    rw [if_neg hsU_lt_192]
    have hsU_toNat_ge_192 : 192 ≤ sU.toNat := by
      by_contra hp; push_neg at hp; apply hsU_lt_192
      rw [UInt64.lt_iff_toNat_lt]; exact hp
    have hsU_toNat_lt_256 : sU.toNat < 256 := by rw [hsU_toNat]; omega
    set s64 : UInt64 := sU - 192
    have hKernel_eq := shift_kernel256_hi_eq qHi qMidHi qMidLo qLo sU s64
              hsU_toNat_ge_192 hsU_toNat_lt_256 rfl
    rw [hKernel_eq, hQuad]
    rw [hmU_toNat, hsU_toNat]
    exact (shiftedSig_v4_eq_widened_core m q k hm_dom hm53_dom hq_lo_dom hq_hi_dom hk_dom
            hm_lt_60 hkLo hkHi hsLo hsHi
            gHi gMid gLo h_t shiftAmt hgHi_def hgMid_def hgLo_def hh_def hshiftAmt_def).symm

/-! ## Hybrid v3b: keep v3 fast path, fall back to v4 instead of spec

`shiftedSig_v3` uses the 128-bit kernel when `qNeg + 4·kPos < 64`
(`B < 2^64`).  Outside, it falls back to the spec `shiftedSig`.  The
spec path dominates the per-call cost (boxed-Nat arithmetic) for ~3 of
23 corpus inputs.  v4 (192-bit) computes those cases in O(1) ns, but
its 4-limb mul has ~50% more multiplies than v3's 3-limb mul, so
csimp'ing every v3 call to v4 regresses the dominant fast-path
inputs.

The hybrid `shiftedSig_v3b` keeps v3's 128-bit fast path and replaces
ONLY the spec-fallback with a v4 call: a 128-bit-when-cheap, 192-bit-
otherwise dispatch with no boxed-Nat fallback at runtime (except for
inputs failing v4's own guards). -/

@[inline]
def shiftedSig_v3b (m : Nat) (q : Int) (k : Int) : Nat :=
  let sigTuple := pow10Lookup128 (-k)
  let sigGHi := sigTuple.1
  let sigGLo := sigTuple.2.1
  let sigH := sigTuple.2.2
  let sigShiftAmt : Int := sigH - q
  let _qNeg : Nat := if q < 0 then (-q).toNat else 0
  let _kPos : Nat := if k ≥ 0 then k.toNat else 0
  if _h_m : m ≥ (1 <<< 60 : Nat) then shiftedSig_v4 m q k
  else if _h_k_lo : (-k : Int) < pow10Table128_kMin then shiftedSig_v4 m q k
  else if _h_k_hi : (-k : Int) > pow10Table128_kMax then shiftedSig_v4 m q k
  else if _h_s_lo : sigShiftAmt < 124 then shiftedSig_v4 m q k
  else if _h_s_hi : sigShiftAmt ≥ 192 then shiftedSig_v4 m q k
  else if _h_dom : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q then
    let mU : UInt64 := UInt64.ofNat m
    let shiftAmtU : UInt64 := UInt64.ofNat sigShiftAmt.toNat
    (shiftedSig_u64_kernel mU sigGHi sigGLo shiftAmtU).toNat
  else
    shiftedSig_v4 m q k

theorem shiftedSig_v3b_eq (m : Nat) (q k : Int) :
    shiftedSig_v3b m q k = shiftedSig m q k := by
  -- v3b is v3 with each spec-fallback replaced by v4.  Since v3 = spec
  -- and v4 = spec, every branch agrees with v3, hence with spec.
  unfold shiftedSig_v3b
  by_cases h_m : m ≥ (1 <<< 60 : Nat)
  · rw [dif_pos h_m]; exact shiftedSig_v4_eq _ _ _
  rw [dif_neg h_m]
  by_cases h_k_lo : (-k : Int) < pow10Table128_kMin
  · rw [dif_pos h_k_lo]; exact shiftedSig_v4_eq _ _ _
  rw [dif_neg h_k_lo]
  by_cases h_k_hi : (-k : Int) > pow10Table128_kMax
  · rw [dif_pos h_k_hi]; exact shiftedSig_v4_eq _ _ _
  rw [dif_neg h_k_hi]
  by_cases h_s_lo : ((pow10Lookup128 (-k)).2.2 - q) < 124
  · rw [dif_pos h_s_lo]; exact shiftedSig_v4_eq _ _ _
  rw [dif_neg h_s_lo]
  by_cases h_s_hi : ((pow10Lookup128 (-k)).2.2 - q) ≥ 192
  · rw [dif_pos h_s_hi]; exact shiftedSig_v4_eq _ _ _
  rw [dif_neg h_s_hi]
  by_cases h_dom : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q
  · rw [dif_pos h_dom]
    -- Reuse the v3 fast-path equality (same binary64-domain branch).
    have hRev : shiftedSig_v3 m q k = shiftedSig m q k := shiftedSig_v3_eq m q k
    unfold shiftedSig_v3 at hRev
    push_neg at h_m h_k_lo h_k_hi h_s_lo h_s_hi
    rw [dif_neg (by omega : ¬ m ≥ (1 <<< 60 : Nat))] at hRev
    rw [dif_neg (by omega : ¬ ((-k : Int) < pow10Table128_kMin))] at hRev
    rw [dif_neg (by omega : ¬ ((-k : Int) > pow10Table128_kMax))] at hRev
    rw [dif_neg (by omega : ¬ ((pow10Lookup128 (-k)).2.2 - q < 124))] at hRev
    rw [dif_neg (by omega : ¬ ((pow10Lookup128 (-k)).2.2 - q ≥ 192))] at hRev
    rw [dif_pos h_dom] at hRev
    exact hRev
  · rw [dif_neg h_dom]; exact shiftedSig_v4_eq _ _ _

/-! ## Wired-in 192-bit path via direct `shiftedSig_v3b` substitution

We do not use `@[csimp]` to redirect `shiftedSig_v3` → `shiftedSig_v3b`
because the chain `toDecimal → shortestUnsigned → shortestUnsigned_v3
→ shortestUnsigned_u64_opt_v2 → shiftedSig_v3` is fully inlined into
the compiled body of `toDecimal_v3` (in `Uint64Bridge.lean`).  The
inlined `shiftedSig_v3` ends up with its slow-path branch calling the
boxed-`Nat` `shiftedSig` spec, with no remaining `shiftedSig_v3` call
site for csimp to rewrite.

Instead, we re-create the path from scratch with `shiftedSig_v3b`
literally substituted in place of `shiftedSig_v3`.  The new
`shortestUnsigned_u64_opt_v3` is a verbatim copy of
`shortestUnsigned_u64_opt_v2` (with `shiftedSig_v3 m q k` →
`shiftedSig_v3b m q k`).  Both compute the same value (proven by
`shiftedSig_v3_eq` and `shiftedSig_v3b_eq`), so the new pipeline is
observationally identical.

The new top-level `toDecimal_v4` then uses this chain, and is wired in
via `@[csimp] @toDecimal = @toDecimal_v4`. -/

@[inline]
def shortestUnsigned_u64_opt_v3 (m : Nat) (q : Int) : Option (UInt64 × Int) :=
  if _h_m : m ≥ (1 <<< 53 : Nat) then none
  else if _h_q_lo : q < (-1074 : Int) then none
  else if _h_q_hi : q > 971 then none
  else
    let irregular := isIrregular m q
    let k := kOfMQ_fast m q
    if _h_k_lo : k < pow10Table128_kMin then none
    else if _h_k_hi : k + 1 > pow10Table128_kMax then none
    else
      let s := shiftedSig_v4 m q k
      if _h_s : s ≥ (1 <<< 57 : Nat) then none
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
          if _h_qh_lo : cmpHQPlusH < 64 then none
          else if _h_qh_hi : cmpHQPlusH > 132 then none
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
                if _h_qh2_lo : cmpQPlusH < 64 then none
                else if _h_qh2_hi : cmpQPlusH > 132 then none
                else
                  let cmpQPlusH8 : UInt64 := UInt64.ofNat cmpQPlusH.toNat
                  match pickNearer_u64_opt cmpGHi cmpGLo cmpQPlusH8 sU mU irregular with
                  | none => none
                  | some chosen => some (chosen, k)
        else if _h_s1 : sU = 0 then none
        else
          let cmpTuple := pow10Lookup128 k
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

theorem shortestUnsigned_u64_opt_v3_eq_v2 (m : Nat) (q : Int) :
    shortestUnsigned_u64_opt_v3 m q = shortestUnsigned_u64_opt_v2 m q := by
  unfold shortestUnsigned_u64_opt_v3 shortestUnsigned_u64_opt_v2
  by_cases h_m : m ≥ (1 <<< 53 : Nat)
  · simp only [dif_pos h_m]
  simp only [dif_neg h_m]
  by_cases h_q_lo : q < (-1074 : Int)
  · simp only [dif_pos h_q_lo]
  simp only [dif_neg h_q_lo]
  by_cases h_q_hi : q > 971
  · simp only [dif_pos h_q_hi]
  simp only [dif_neg h_q_hi]
  by_cases h_k_lo : kOfMQ_fast m q < pow10Table128_kMin
  · simp only [dif_pos h_k_lo]
  simp only [dif_neg h_k_lo]
  by_cases h_k_hi : kOfMQ_fast m q + 1 > pow10Table128_kMax
  · simp only [dif_pos h_k_hi]
  simp only [dif_neg h_k_hi]
  -- Now the key step: shiftedSig_v4 m q k = shiftedSig_v3 m q k.
  have hRewrite : shiftedSig_v4 m q (kOfMQ_fast m q) = shiftedSig_v3 m q (kOfMQ_fast m q) := by
    rw [shiftedSig_v4_eq, ← shiftedSig_v3_eq]
  rw [hRewrite]
  rfl

@[inline]
def shortestUnsigned_v4 (m : Nat) (q : Int) : Nat × Int :=
  match shortestUnsigned_u64_opt_v3 m q with
  | some (sU, k) => (sU.toNat, k)
  | none => shortestUnsigned_packed m q

theorem shortestUnsigned_v4_eq (m : Nat) (q : Int) :
    shortestUnsigned_v4 m q = shortestUnsigned m q := by
  unfold shortestUnsigned_v4
  rw [shortestUnsigned_u64_opt_v3_eq_v2]
  -- Now shortestUnsigned_v4 has the same body as shortestUnsigned_v3.
  -- Use shortestUnsigned_v3_eq.
  show (match shortestUnsigned_u64_opt_v2 m q with
        | some (sU, k) => (sU.toNat, k)
        | none => shortestUnsigned_packed m q) = shortestUnsigned m q
  have hRev : shortestUnsigned_v3 m q = shortestUnsigned m q := shortestUnsigned_v3_eq m q
  unfold shortestUnsigned_v3 at hRev
  exact hRev

/-! ## Fused `toDecimal_v4`

Calls `shortestUnsigned_v4` directly (which uses `shiftedSig_v3b` via
the new chain).  Compiled in this file, AFTER `shiftedSig_v3b` is in
scope. -/

open Srtfp.Float in
def toDecimal_v4 (f : _root_.Float) : Except String _root_.Srtfp.Decimal :=
  if isNaNBits f then
    .error "NaN"
  else if isInfBits f then
    .error (if signBit f then "-Infinity" else "Infinity")
  else
    let d := decode f
    if d.m = 0 then .ok ⟨d.sign, 0, 0⟩
    else
      let (sig, exp) := shortestUnsigned_v4 d.m d.q
      .ok (Srtfp.Decimal.mk' d.sign sig exp)

theorem toDecimal_v4_eq (f : _root_.Float) :
    toDecimal_v4 f = toDecimal f := by
  unfold toDecimal_v4 toDecimal
  by_cases h1 : Srtfp.Float.isNaNBits f = true
  · simp [h1]
  by_cases h2 : Srtfp.Float.isInfBits f = true
  · simp [h1, h2]
  simp only [h1, h2, if_false, Bool.false_eq_true]
  by_cases h3 : (Srtfp.Float.decode f).m = 0
  · simp [h3]
  simp only [h3, if_false]
  rw [shortestUnsigned_v4_eq]

-- Superseded registration: `toDecimal_eq_v7_csimp` (KernelV6.lean) is the live @[csimp].
theorem toDecimal_eq_v4_csimp : @toDecimal = @toDecimal_v4 := by
  funext f
  exact (toDecimal_v4_eq f).symm

end Srtfp.Schubfach
