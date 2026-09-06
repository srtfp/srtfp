module
/- The reference reader in `Nat` arithmetic.

   `Reader.read` works in `Rat`: the magnitude `x = m · 10^e`, the grid
   exponent from `⌊x · 2^1074⌋`, the significand as the half-even
   rounding of `x / 2^k`. Every step is a comparison or a floor of a
   quotient of naturals, so the same computation runs on `Nat` with
   `x = N / D`, `N = m · 10^max(e,0)`, `D = 10^max(-e,0)`: a handful of
   big-integer operations instead of rational arithmetic with `gcd`s.

   This is the fallback of the fast reader (`Srtfp/Perf/ReadFast.lean`)
   and the first rung of its proof. `readExact_eq` shows it is `read`,
   through the two characterisations `gridExp_eq_of` and
   `roundEven_eq_of`: the facts `gridExp_spec` and `roundEven_spec` state
   pin their values, so it suffices to check them for the `Nat`
   quantities. -/

public import Srtfp.Proofs.Reader.Compute

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Reader

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-! ## The characterisations pin the values -/

/-- The four facts of `roundEven_spec` determine `roundEven x`. -/
theorem roundEven_eq_of {x : Rat} {n : Int}
    (h1 : (n : Rat) - 1/2 ≤ x) (h2 : x ≤ n + 1/2)
    (h3 : x = n - 1/2 → n % 2 = 0) (h4 : x = n + 1/2 → n % 2 = 0) :
    roundEven x = n := by
  obtain ⟨r1, r2, r3, r4⟩ := roundEven_spec x
  generalize roundEven x = r at *
  have hle1 : r ≤ n + 1 := by
    have h : (r : Rat) ≤ ((n + 1 : Int) : Rat) := by push_cast; grind
    exact_mod_cast h
  have hle2 : n ≤ r + 1 := by
    have h : (n : Rat) ≤ ((r + 1 : Int) : Rat) := by push_cast; grind
    exact_mod_cast h
  rcases Int.lt_trichotomy r n with hlt | heq | hgt
  · exfalso
    have hr : ((r : Int) : Rat) = (n : Rat) - 1 := by exact_mod_cast (show r = n - 1 by omega)
    have hx : x = (n : Rat) - 1/2 := by grind
    have := h3 hx
    have := r4 (by grind)
    omega
  · exact heq
  · exfalso
    have hr : ((r : Int) : Rat) = (n : Rat) + 1 := by exact_mod_cast (show r = n + 1 by omega)
    have hx : x = (n : Rat) + 1/2 := by grind
    have := h4 hx
    have := r3 (by grind)
    omega

/-- `roundEven_eq_of` for a natural candidate. -/
theorem roundEven_eq_natCast_of {x : Rat} {n : Nat}
    (h1 : (n : Rat) - 1/2 ≤ x) (h2 : x ≤ n + 1/2)
    (h3 : x = n - 1/2 → n % 2 = 0) (h4 : x = n + 1/2 → n % 2 = 0) :
    roundEven x = n := by
  apply roundEven_eq_of (n := (n : Int))
  · rw [Rat.intCast_natCast]; exact h1
  · rw [Rat.intCast_natCast]; exact h2
  · rw [Rat.intCast_natCast]; intro h; have := h3 h; omega
  · rw [Rat.intCast_natCast]; intro h; have := h4 h; omega

/-- The three facts of `gridExp_spec` determine `gridExp x`. -/
theorem gridExp_eq_of {x : Rat} (hx : 0 ≤ x) {k : Int} (h1 : -1074 ≤ k)
    (h2 : x < (2 : Rat) ^ (k + 53)) (h3 : k = -1074 ∨ (2 : Rat) ^ (k + 52) ≤ x) :
    gridExp x = k := by
  obtain ⟨g1, g2, g3⟩ := gridExp_spec hx
  generalize gridExp x = g at *
  rcases Int.lt_trichotomy g k with hlt | heq | hgt
  · exfalso
    have hk : (2 : Rat) ^ (k + 52) ≤ x := by
      rcases h3 with h | h
      · omega
      · exact h
    have hmono : (2 : Rat) ^ (g + 53) ≤ (2 : Rat) ^ (k + 52) :=
      zpow_le_zpow_right₀ (by decide) (by omega)
    exact absurd hk (Rat.not_le.mpr (lt_of_lt_of_le g2 hmono))
  · exact heq
  · exfalso
    have hg : (2 : Rat) ^ (g + 52) ≤ x := by
      rcases g3 with h | h
      · omega
      · exact h
    have hmono : (2 : Rat) ^ (k + 53) ≤ (2 : Rat) ^ (g + 52) :=
      zpow_le_zpow_right₀ (by decide) (by omega)
    exact absurd hg (Rat.not_le.mpr (lt_of_lt_of_le h2 hmono))

/-! ## Quotients of naturals -/

/-- `roundEven (p / q)` for naturals with `0 < q`: `⌊(2p + q) / 2q⌋`, one
    less on an odd tie. -/
def roundEvenNat (p q : Nat) : Nat :=
  let n := (2 * p + q) / (2 * q)
  if (2 * p + q) % (2 * q) = 0 ∧ n % 2 = 1 then n - 1 else n

theorem half_le_div {a b c : Nat} (hc : 0 < c) :
    ((a : Rat) - 1/2 ≤ (b : Rat) / c) ↔ 2 * (a * c) ≤ 2 * b + c := by
  have hcR : (0 : Rat) < c := by exact_mod_cast hc
  rw [le_div_iff hcR, ← Rat.natCast_le_natCast]
  push_cast
  constructor <;> intro h <;> grind

theorem div_le_half {a b c : Nat} (hc : 0 < c) :
    ((b : Rat) / c ≤ (a : Rat) + 1/2) ↔ 2 * b ≤ 2 * (a * c) + c := by
  have hcR : (0 : Rat) < c := by exact_mod_cast hc
  rw [div_le_iff hcR, ← Rat.natCast_le_natCast]
  push_cast
  constructor <;> intro h <;> grind

theorem div_eq_sub_half {a b c : Nat} (hc : 0 < c) :
    ((b : Rat) / c = (a : Rat) - 1/2) ↔ 2 * b + c = 2 * (a * c) := by
  have hcR : (0 : Rat) < c := by exact_mod_cast hc
  rw [div_eq_iff hcR, ← Rat.natCast_inj]
  push_cast
  constructor <;> intro h <;> grind

theorem div_eq_add_half {a b c : Nat} (hc : 0 < c) :
    ((b : Rat) / c = (a : Rat) + 1/2) ↔ 2 * b = 2 * (a * c) + c := by
  have hcR : (0 : Rat) < c := by exact_mod_cast hc
  rw [div_eq_iff hcR, ← Rat.natCast_inj]
  push_cast
  constructor <;> intro h <;> grind

theorem roundEven_div (p q : Nat) (hq : 0 < q) :
    roundEven ((p : Rat) / q) = roundEvenNat p q := by
  have hdm := Nat.div_add_mod (2 * p + q) (2 * q)
  have hr := Nat.mod_lt (2 * p + q) (by omega : 0 < 2 * q)
  unfold roundEvenNat
  dsimp only
  generalize (2 * p + q) / (2 * q) = n0 at *
  generalize (2 * p + q) % (2 * q) = r at *
  split
  · rename_i h
    obtain ⟨hr0, hodd⟩ := h
    subst hr0
    obtain ⟨n', rfl⟩ : ∃ n', n0 = n' + 1 := ⟨n0 - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    apply roundEven_eq_natCast_of
    · rw [half_le_div hq]; grind
    · rw [div_le_half hq]; grind
    · rw [div_eq_sub_half hq]; intro h; exfalso; grind
    · intro _; omega
  · rename_i h
    apply roundEven_eq_natCast_of
    · rw [half_le_div hq]; grind
    · rw [div_le_half hq]; grind
    · rw [div_eq_sub_half hq]; intro h'
      have : r = 0 := by grind
      subst this
      have : ¬ n0 % 2 = 1 := fun ho => h ⟨rfl, ho⟩
      omega
    · rw [div_eq_add_half hq]; intro h'; exfalso; grind

/-- `2^j · 2^1074` as a natural power, for `-1074 ≤ j`. -/
theorem two_zpow_mul_two_pow (j : Int) (hj : -1074 ≤ j) :
    (2 : Rat) ^ j * (2 : Rat) ^ (1074 : Nat) = (2 : Rat) ^ ((j + 1074).toNat : Nat) := by
  rw [← Rat.zpow_natCast, ← Rat.zpow_add (by decide), ← Rat.zpow_natCast,
    Int.toNat_of_nonneg (by omega)]
  try simp

/-- `2^j` against a quotient, scaled to naturals by `2^1074`. -/
theorem div_lt_two_zpow_iff {N D : Nat} (hD : 0 < D) {j : Int} (hj : -1074 ≤ j) :
    ((N : Rat) / D < (2 : Rat) ^ j) ↔ N * 2 ^ 1074 < 2 ^ (j + 1074).toNat * D := by
  have hDR : (0 : Rat) < D := by exact_mod_cast hD
  have hP : (0 : Rat) < (2 : Rat) ^ (1074 : Nat) := Rat.pow_pos (by decide)
  have h2j := two_zpow_mul_two_pow j hj
  have hcast := @Rat.natCast_lt_natCast (N * 2 ^ 1074) (2 ^ (j + 1074).toNat * D)
  push_cast at hcast
  rw [← hcast, Rat.div_lt_iff hDR]
  constructor
  · intro h
    have h1 := Rat.mul_lt_mul_of_pos_right h hP
    rw [show (2 : Rat) ^ j * D * 2 ^ (1074 : Nat) = 2 ^ j * 2 ^ (1074 : Nat) * D by grind, h2j] at h1
    exact h1
  · intro h
    rcases lt_or_ge (N : Rat) (2 ^ j * D) with h' | h'
    · exact h'
    have hc' := Rat.mul_le_mul_of_nonneg_right h' (Rat.le_of_lt hP)
    rw [show (2 : Rat) ^ j * D * 2 ^ (1074 : Nat) = 2 ^ j * 2 ^ (1074 : Nat) * D by grind, h2j] at hc'
    exact absurd h (Rat.not_lt.mpr hc')

theorem two_zpow_le_div_iff {N D : Nat} (hD : 0 < D) {j : Int} (hj : -1074 ≤ j) :
    ((2 : Rat) ^ j ≤ (N : Rat) / D) ↔ 2 ^ (j + 1074).toNat * D ≤ N * 2 ^ 1074 := by
  have hDR : (0 : Rat) < D := by exact_mod_cast hD
  have hP : (0 : Rat) < (2 : Rat) ^ (1074 : Nat) := Rat.pow_pos (by decide)
  have h2j := two_zpow_mul_two_pow j hj
  have hcast := @Rat.natCast_le_natCast (2 ^ (j + 1074).toNat * D) (N * 2 ^ 1074)
  push_cast at hcast
  rw [← hcast, le_div_iff hDR]
  constructor
  · intro h
    have h1 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hP)
    rw [show (2 : Rat) ^ j * D * 2 ^ (1074 : Nat) = 2 ^ j * 2 ^ (1074 : Nat) * D by grind, h2j] at h1
    exact h1
  · intro h
    rcases lt_or_ge (N : Rat) (2 ^ j * D) with h' | h'
    · have hc' := Rat.mul_lt_mul_of_pos_right h' hP
      rw [show (2 : Rat) ^ j * D * 2 ^ (1074 : Nat) = 2 ^ j * 2 ^ (1074 : Nat) * D by grind, h2j] at hc'
      exact absurd hc' (Rat.not_lt.mpr h)
    · exact h'

/-! ## The reader -/

/-- `read` on a sign and a magnitude: the body of `read`. -/
def readMag (s : Sign) (x : Rat) : UnpackedFloat :=
  if 2 ^ 1024 - 2 ^ 970 ≤ x then .infinity s
  else
    let k := gridExp x
    let n := (roundEven (x / 2 ^ k)).toNat
    if h : n = 0 then .zero s
    else if n = 2 ^ 53 then .finite s (2 ^ 52) (k + 1) (by decide)
    else .finite s n k (Nat.pos_of_ne_zero h)

theorem read_eq_readMag (d : Decimal) : read d = readMag d.sign (Rat.abs (Spec.toRat d)) := rfl

/-- `Reader.read` in `Nat` arithmetic: `x = N / D`. -/
def readExact (d : Decimal) : UnpackedFloat :=
  let N := d.significand * 10 ^ d.exponent.toNat
  let D := 10 ^ (-d.exponent).toNat
  if 2 ^ 1024 * D ≤ N + 2 ^ 970 * D then .infinity d.sign
  else
    let Y := N * 2 ^ 1074 / D
    let k : Int := max ((Y.log2 : Int) - 1126) (-1074)
    let n := if 0 ≤ k then roundEvenNat N (D * 2 ^ k.toNat) else roundEvenNat (N * 2 ^ (-k).toNat) D
    if h : n = 0 then .zero d.sign
    else if n = 2 ^ 53 then .finite d.sign (2 ^ 52) (k + 1) (by decide)
    else .finite d.sign n k (Nat.pos_of_ne_zero h)

/-- The magnitude of a decimal as a quotient of naturals. -/
theorem abs_toRat_div (d : Decimal) :
    Rat.abs (Spec.toRat d)
      = ((d.significand * 10 ^ d.exponent.toNat : Nat) : Rat) / ((10 ^ (-d.exponent).toNat : Nat) : Rat) := by
  rw [abs_toRat]
  by_cases he : 0 ≤ d.exponent
  · generalize hn : d.exponent.toNat = n
    rw [show (-d.exponent).toNat = 0 by omega, Nat.pow_zero, show d.exponent = (n : Int) by omega,
      Rat.zpow_natCast]
    push_cast
    rw [Rat.div_def, Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1), Rat.mul_one]
  · generalize hn : (-d.exponent).toNat = n
    rw [show d.exponent.toNat = 0 by omega, Nat.pow_zero, Nat.mul_one,
      show d.exponent = -(n : Int) by omega, Rat.zpow_neg, Rat.zpow_natCast]
    push_cast
    rw [Rat.div_def]

theorem readExact_eq (d : Decimal) : readExact d = read d := by
  unfold readExact read
  dsimp only
  rw [abs_toRat_div]
  generalize hN : d.significand * 10 ^ d.exponent.toNat = N
  generalize hD : 10 ^ (-d.exponent).toNat = D
  have hD0 : 0 < D := by rw [← hD]; exact Nat.pow_pos (by decide)
  have hDR : (0 : Rat) < D := by exact_mod_cast hD0
  -- the overflow threshold
  have hthr : ((2 : Rat) ^ 1024 - 2 ^ 970 ≤ (N : Rat) / D) ↔ 2 ^ 1024 * D ≤ N + 2 ^ 970 * D := by
    rw [le_div_iff hDR, ← Rat.natCast_le_natCast]
    push_cast
    generalize (2 : Rat) ^ 1024 = A
    generalize (2 : Rat) ^ 970 = B
    constructor <;> intro h <;> grind
  by_cases hover : 2 ^ 1024 * D ≤ N + 2 ^ 970 * D
  · rw [if_pos hover, if_pos (hthr.mpr hover)]
  rw [if_neg hover, if_neg (fun h => hover (hthr.mp h))]
  -- the grid exponent
  generalize hY : N * 2 ^ 1074 / D = Y
  have hYlo : Y * D ≤ N * 2 ^ 1074 := by rw [← hY]; exact Nat.div_mul_le_self _ _
  have hYhi : N * 2 ^ 1074 < (Y + 1) * D := by
    rw [← hY, Nat.mul_comm (N * 2 ^ 1074 / D + 1) D]; exact Nat.lt_mul_div_succ _ hD0
  generalize hL : Y.log2 = L
  have hL1 : Y < 2 ^ (L + 1) := by rw [← hL]; exact Nat.lt_log2_self
  have hL2 : Y ≠ 0 → 2 ^ L ≤ Y := fun h => by rw [← hL]; exact Nat.log2_self_le h
  have hk : gridExp ((N : Rat) / D) = max ((L : Int) - 1126) (-1074) := by
    apply gridExp_eq_of (div_nonneg Rat.natCast_nonneg hDR)
    · omega
    · rw [div_lt_two_zpow_iff hD0 (by omega)]
      have h1 : N * 2 ^ 1074 < 2 ^ (L + 1) * D :=
        Nat.lt_of_lt_of_le hYhi (Nat.mul_le_mul_right _ hL1)
      have h2 : 2 ^ (L + 1) ≤ 2 ^ (max ((L : Int) - 1126) (-1074) + 53 + 1074).toNat :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)
    · by_cases hL52 : 52 ≤ L
      · right
        rw [two_zpow_le_div_iff hD0 (by omega), show (max ((L : Int) - 1126) (-1074) + 52 + 1074).toNat = L by omega]
        have hY0 : Y ≠ 0 := by
          intro h; rw [h, Nat.log2_zero] at hL; omega
        exact Nat.le_trans (Nat.mul_le_mul_right _ (hL2 hY0)) hYlo
      · left; omega
  rw [hk]
  generalize max ((L : Int) - 1126) (-1074) = k at *
  -- the significand
  have hn : (roundEven ((N : Rat) / D / (2 : Rat) ^ k)).toNat
      = if 0 ≤ k then roundEvenNat N (D * 2 ^ k.toNat) else roundEvenNat (N * 2 ^ (-k).toNat) D := by
    split
    · rename_i hk0
      generalize hkn : k.toNat = kn
      have hk' : k = (kn : Int) := by omega
      rw [show (N : Rat) / D / (2 : Rat) ^ k = (N : Rat) / ((D * 2 ^ kn : Nat) : Rat) by
        rw [hk', Rat.zpow_natCast]; push_cast
        rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.inv_mul_rev, Rat.mul_comm (2 ^ kn : Rat)⁻¹]]
      rw [roundEven_div _ _ (Nat.mul_pos hD0 (Nat.pow_pos (by decide)))]
      exact Int.toNat_natCast _
    · rename_i hk0
      generalize hkn : (-k).toNat = kn
      have hk' : k = -(kn : Int) := by omega
      rw [show (N : Rat) / D / (2 : Rat) ^ k = ((N * 2 ^ kn : Nat) : Rat) / D by
        rw [hk', Rat.zpow_neg, Rat.zpow_natCast]; push_cast
        rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_inv]; grind]
      rw [roundEven_div _ _ hD0]
      exact Int.toNat_natCast _
  simp only [hn]
