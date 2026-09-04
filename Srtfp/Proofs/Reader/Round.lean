module
/- The three arithmetic helpers of `Srtfp/Clinger.lean`, read over Rat:
   `roundNearestEven` is the nearest integer with ties to even,
   `findBinaryExp` the binary exponent, `scaleByPow2` an exact rescaling. -/
public import Srtfp.Clinger
public import Srtfp.Proofs.Printer.Interval

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Clinger

open Srtfp.Printer

/-! ## Division, multiplicatively -/

theorem le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [← not_lt, ← not_lt, Rat.div_lt_iff hc]

theorem div_eq_iff {a b c : Rat} (hc : 0 < c) : a / c = b ↔ a = b * c := by
  constructor
  · intro h; rw [← h, Rat.div_mul_cancel (by grind)]
  · intro h; rw [h, Rat.mul_div_cancel (by grind)]

/-! ## `roundNearestEven` -/

/-- `n = roundNearestEven num denom` is the integer nearest to `t = num / denom`:
`n - 1/2 ≤ t ≤ n + 1/2`, and an endpoint is attained only for even `n`. -/
theorem roundNearestEven_spec {num denom : Nat} (hd : 0 < denom) :
    let n := roundNearestEven num denom
    let t : Rat := (num : Rat) / denom
    (n : Rat) - 1/2 ≤ t ∧ t ≤ n + 1/2
      ∧ (t = n - 1/2 → n % 2 = 0) ∧ (t = n + 1/2 → n % 2 = 0) := by
  intro n t
  -- `num = q · denom + r` with `0 ≤ r < denom`; `t = q + ρ` with `ρ = r / denom`
  have hdm := Nat.div_add_mod num denom
  rw [Nat.mul_comm] at hdm
  have hmod : num - num / denom * denom = num % denom :=
    Nat.sub_eq_of_eq_add (by rw [Nat.add_comm]; exact hdm.symm)
  have hD : (0 : Rat) < denom := by exact_mod_cast hd
  have hnum : (num : Rat) = (num / denom : Nat) * denom + (num % denom : Nat) := by
    exact_mod_cast hdm.symm
  have ht : t = (num / denom : Nat) + ((num % denom : Nat) : Rat) / denom := by
    show (num : Rat) / denom = _
    rw [div_eq_iff hD, hnum, Rat.add_mul, Rat.div_mul_cancel (by grind)]
  generalize hρ : ((num % denom : Nat) : Rat) / denom = ρ at ht
  have hρ0 : 0 ≤ ρ := by
    rw [← hρ, le_div_iff hD, Rat.zero_mul]; exact_mod_cast Nat.zero_le _
  have hρ1 : ρ < 1 := by
    rw [← hρ, Rat.div_lt_iff hD, Rat.one_mul]; exact_mod_cast Nat.mod_lt num hd
  have hlt : 2 * (num % denom) < denom ↔ ρ < 1/2 := by
    rw [← hρ, Rat.div_lt_iff hD]
    constructor
    · intro h; have : 2 * ((num % denom : Nat) : Rat) < denom := by exact_mod_cast h
      grind
    · intro h; have : 2 * ((num % denom : Nat) : Rat) < denom := by grind
      exact_mod_cast this
  have hgt : denom < 2 * (num % denom) ↔ 1/2 < ρ := by
    rw [← hρ, Rat.lt_div_iff hD]
    constructor
    · intro h; have : (denom : Rat) < 2 * ((num % denom : Nat) : Rat) := by exact_mod_cast h
      grind
    · intro h; have : (denom : Rat) < 2 * ((num % denom : Nat) : Rat) := by grind
      exact_mod_cast this
  have heq : 2 * (num % denom) = denom ↔ ρ = 1/2 := by
    rw [← hρ, div_eq_iff hD]
    constructor
    · intro h; have : 2 * ((num % denom : Nat) : Rat) = denom := by exact_mod_cast h
      grind
    · intro h; have : 2 * ((num % denom : Nat) : Rat) = denom := by grind
      exact_mod_cast this
  show (roundNearestEven num denom : Rat) - 1/2 ≤ t ∧ t ≤ roundNearestEven num denom + 1/2
      ∧ (t = roundNearestEven num denom - 1/2 → roundNearestEven num denom % 2 = 0)
      ∧ (t = roundNearestEven num denom + 1/2 → roundNearestEven num denom % 2 = 0)
  unfold roundNearestEven
  simp only [hmod]
  generalize num / denom = q at ht ⊢
  generalize num % denom = r at hlt hgt heq ⊢
  rw [ht]
  by_cases h1 : 2 * r < denom
  · rw [if_pos h1]; have := hlt.mp h1
    refine ⟨by grind, by grind, fun h => by grind, fun h => by grind⟩
  · rw [if_neg h1]
    by_cases h2 : 2 * r > denom
    · rw [if_pos h2]; have := hgt.mp (by omega); push_cast
      refine ⟨by grind, by grind, fun h => by grind, fun h => by grind⟩
    · rw [if_neg h2]
      have := heq.mp (by omega)
      by_cases h3 : q % 2 = 0
      · rw [if_pos h3]
        refine ⟨by grind, by grind, fun h => by grind, fun _ => h3⟩
      · rw [if_neg h3]; push_cast
        refine ⟨by grind, by grind, fun _ => by omega, fun h => by grind⟩

/-- `roundNearestEven` never strays beyond the unit around `t`. -/
theorem roundNearestEven_bounds {num denom : Nat} (hd : 0 < denom) {lo hi : Nat}
    (hlo : (lo : Rat) ≤ (num : Rat) / denom) (hhi : (num : Rat) / denom < hi) :
    lo ≤ roundNearestEven num denom ∧ roundNearestEven num denom ≤ hi := by
  obtain ⟨h1, h2, -, -⟩ := roundNearestEven_spec (num := num) hd
  constructor
  · have : (lo : Rat) < roundNearestEven num denom + 1 := by grind
    exact_mod_cast (Nat.lt_succ_iff.mp (by exact_mod_cast this))
  · have : (roundNearestEven num denom : Rat) < hi + 1 := by grind
    exact_mod_cast (Nat.lt_succ_iff.mp (by exact_mod_cast this))

/-! ## `findBinaryExp` -/

theorem leBy2e_iff (a b : Nat) (e : Int) :
    leBy2e a b e = true ↔ (2 : Rat) ^ e * b ≤ a := by
  unfold leBy2e
  by_cases he : e ≥ 0
  · rw [if_pos he, two_zpow_toNat he, decide_eq_true_eq]
    constructor
    · intro h
      have : ((b * 2 ^ e.toNat : Nat) : Rat) ≤ a := by exact_mod_cast h
      push_cast at this; grind
    · intro h
      have : ((b * 2 ^ e.toNat : Nat) : Rat) ≤ a := by push_cast; grind
      exact_mod_cast this
  · rw [if_neg he, decide_eq_true_eq]
    have hN : (2 : Rat) ^ (-e) = (2 : Rat) ^ (-e).toNat := two_zpow_toNat (by omega)
    have hpos := two_zpow_pos e
    have hposn := two_zpow_pos (-e)
    have hcancel := two_zpow_mul_neg e
    constructor
    · intro h
      have h' : (b : Rat) ≤ a * (2 : Rat) ^ (-e) := by rw [hN]; exact_mod_cast h
      have := Rat.mul_le_mul_of_nonneg_left h' (le_of_lt hpos)
      have hrew : (2 : Rat) ^ e * (a * (2 : Rat) ^ (-e)) = a := by
        rw [Rat.mul_comm (a : Rat), ← Rat.mul_assoc, hcancel, Rat.one_mul]
      rw [hrew] at this; exact this
    · intro h
      have := Rat.mul_le_mul_of_nonneg_left h (le_of_lt hposn)
      have hrew : (2 : Rat) ^ (-e) * ((2 : Rat) ^ e * b) = b := by
        rw [← Rat.mul_assoc, Rat.mul_comm ((2 : Rat) ^ (-e)), hcancel, Rat.one_mul]
      rw [hrew, Rat.mul_comm, hN] at this
      exact_mod_cast this

/-- `e = findBinaryExp a b` is the exponent with `2^e ≤ a / b < 2^(e+1)`. -/
theorem findBinaryExp_spec {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    (2 : Rat) ^ findBinaryExp a b * b ≤ a ∧ (a : Rat) < (2 : Rat) ^ (findBinaryExp a b + 1) * b := by
  unfold findBinaryExp
  generalize hE : (Nat.log2 a : Int) - (Nat.log2 b : Int) = E
  have hA1 : (2 : Rat) ^ E * (2 : Rat) ^ (Nat.log2 b : Int) ≤ a := by
    rw [← Rat.zpow_add (by decide), show E + Nat.log2 b = Nat.log2 a by omega, Rat.zpow_natCast]
    exact_mod_cast Nat.log2_self_le (by omega)
  have hA2 : (a : Rat) < (2 : Rat) ^ (E + 1) * (2 : Rat) ^ (Nat.log2 b : Int) := by
    rw [← Rat.zpow_add (by decide), show E + 1 + Nat.log2 b = ((Nat.log2 a + 1 : Nat) : Int) by omega,
      Rat.zpow_natCast]
    exact_mod_cast Nat.lt_log2_self
  have hB1 : (2 : Rat) ^ (Nat.log2 b : Int) ≤ b := by
    rw [Rat.zpow_natCast]; exact_mod_cast Nat.log2_self_le (by omega)
  have hB2 : (b : Rat) < (2 : Rat) ^ (Nat.log2 b : Int) * 2 := by
    rw [← Rat.zpow_add_one (by decide), show (Nat.log2 b : Int) + 1 = ((Nat.log2 b + 1 : Nat) : Int) by omega,
      Rat.zpow_natCast]
    exact_mod_cast Nat.lt_log2_self
  have hpB := two_zpow_pos (Nat.log2 b : Int)
  have hpE := two_zpow_pos E
  have hpE1 := two_zpow_pos (E + 1)
  have hpE' := two_zpow_pos (E - 1)
  have hsplit : (2 : Rat) ^ (E + 1) = 2 ^ E * 2 := Rat.zpow_add_one (by decide) E
  have hsplit' : (2 : Rat) ^ (E - 1) * 2 = 2 ^ E := by
    rw [← Rat.zpow_add_one (by decide), Int.sub_add_cancel]
  have hbpos : (0 : Rat) < b := by exact_mod_cast hb
  have h2 : (2 : Rat) ^ (E - 1) * ((2 : Rat) ^ (Nat.log2 b : Int) * 2) = 2 ^ E * 2 ^ (Nat.log2 b : Int) := by
    rw [Rat.mul_comm ((2 : Rat) ^ (Nat.log2 b : Int)), ← Rat.mul_assoc, hsplit']
  have h3 := Rat.mul_le_mul_of_nonneg_left hB1 (le_of_lt hpE1)
  have h4 := Rat.mul_lt_mul_of_pos_left hB2 hpE'
  rw [h2] at h4
  by_cases h : leBy2e a b E = true
  · rw [if_pos h]
    refine ⟨(leBy2e_iff a b E).mp h, ?_⟩
    generalize (2 : Rat) ^ (E + 1) = PE1 at *
    generalize (2 : Rat) ^ (Nat.log2 b : Int) = PB at *
    grind
  · rw [if_neg h]
    have h' : ¬ (2 : Rat) ^ E * b ≤ a := fun hle => h ((leBy2e_iff a b E).mpr hle)
    rw [Int.sub_add_cancel]
    generalize (2 : Rat) ^ (E - 1) = PE' at *
    generalize (2 : Rat) ^ E = PE at *
    generalize (2 : Rat) ^ (Nat.log2 b : Int) = PB at *
    grind

/-! ## `scaleByPow2` -/

/-- `scaleByPow2 a b k` is `(a / b) · 2^k` as a fraction with positive denominator. -/
theorem scaleByPow2_spec {a b : Nat} (hb : 0 < b) (k : Int) :
    0 < (scaleByPow2 a b k).2
      ∧ ((scaleByPow2 a b k).1 : Rat) / (scaleByPow2 a b k).2 = (a : Rat) / b * (2 : Rat) ^ k := by
  unfold scaleByPow2
  have hbq : (0 : Rat) < b := by exact_mod_cast hb
  by_cases hk : k ≥ 0
  · rw [if_pos hk]
    refine ⟨hb, ?_⟩
    simp only
    rw [two_zpow_toNat hk, div_eq_iff hbq]
    push_cast
    rw [Rat.mul_assoc, Rat.mul_comm ((2 : Rat) ^ k.toNat) b, ← Rat.mul_assoc, Rat.div_mul_cancel (by grind)]
  · rw [if_neg hk]
    have hN : (2 : Rat) ^ (-k) = (2 : Rat) ^ (-k).toNat := two_zpow_toNat (by omega)
    have hpos : (0 : Rat) < (2 : Rat) ^ (-k) := two_zpow_pos _
    have hpk : (0 : Rat) < (2 : Rat) ^ k := two_zpow_pos _
    refine ⟨Nat.mul_pos hb (Nat.pow_pos (by decide)), ?_⟩
    simp only
    have hD : (0 : Rat) < ((b * 2 ^ (-k).toNat : Nat) : Rat) := by
      exact_mod_cast Nat.mul_pos hb (Nat.pow_pos (by decide))
    rw [div_eq_iff hD]
    push_cast
    rw [← hN]
    have hcancel := two_zpow_mul_neg k
    calc (a : Rat) = (a : Rat) / b * b := by rw [Rat.div_mul_cancel (by grind)]
      _ = (a : Rat) / b * (2 : Rat) ^ k * (b * (2 : Rat) ^ (-k)) := by
          rw [Rat.mul_assoc ((a : Rat) / b), Rat.mul_comm (b : Rat), ← Rat.mul_assoc ((2 : Rat) ^ k),
            hcancel, Rat.one_mul]

end Srtfp.Clinger
