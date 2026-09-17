module
/- Characterizations of the reference reader's arithmetic, shared by the
   upstream-model equivalence proof and the fast reader's correctness proof. -/

public import Srtfp.Proofs.Reader.Compute

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Reader

open Srtfp.Printer Srtfp.Model
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
  have hle1 : r ≤ n + 1 := by exact_mod_cast (show (r : Rat) ≤ ((n + 1 : Int) : Rat) by push_cast; grind)
  have hle2 : n ≤ r + 1 := by exact_mod_cast (show (n : Rat) ≤ ((r + 1 : Int) : Rat) by push_cast; grind)
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

/-- Strictly inside `(n - 1/2, n + 1/2)`: no tie, so `roundEven` is `n`. -/
theorem roundEven_eq_of_strict {y : Rat} {n : Nat}
    (h1 : (n : Rat) - 1/2 < y) (h2 : y < n + 1/2) : roundEven y = n :=
  roundEven_eq_natCast_of (Rat.le_of_lt h1) (Rat.le_of_lt h2)
    (fun h => absurd h (Rat.ne_of_gt h1)) (fun h => absurd h (Rat.ne_of_lt h2))

/-- `X / D` rounds to `n` when `(2n - 1) D < 2X < (2n + 1) D`. -/
theorem roundEven_eq_of_between {X : Rat} {D n : Nat} (hD : 0 < D)
    (hlo : ((2 * n : Nat) : Rat) * D < 2 * X + D) (hhi : 2 * X < ((2 * n + 1 : Nat) : Rat) * D) :
    roundEven (X / D) = n := by
  have hDR : (0 : Rat) < D := by exact_mod_cast hD
  apply roundEven_eq_of_strict
  · rw [Rat.lt_div_iff hDR]; push_cast at hlo ⊢; grind
  · rw [Rat.div_lt_iff hDR]; push_cast at hhi ⊢; grind

/-- A tie `Q + 1/2` rounds to the even neighbour. -/
theorem roundEven_tie (Q : Nat) : roundEven ((Q : Rat) + 1/2) = ((Q + Q % 2 : Nat) : Int) := by
  rcases Nat.mod_two_eq_zero_or_one Q with h | h <;> simp only [h, Nat.add_zero]
  · exact roundEven_eq_natCast_of (by grind) (Rat.le_refl) (fun h' => by grind) (fun _ => h)
  · exact roundEven_eq_natCast_of (by push_cast; grind) (by push_cast; grind) (fun _ => by omega)
      (fun h' => by push_cast at h'; grind)

/-- Above a natural bound `b`, the rounding stays at or above `b`. -/
theorem roundEven_ge {y : Rat} {b : Nat} (hy : (b : Rat) ≤ y) : (b : Int) ≤ roundEven y := by
  have h := (roundEven_spec y).2.1
  have : ((b : Int) : Rat) < roundEven y + 1 := by push_cast; grind
  have : (b : Int) < roundEven y + 1 := by exact_mod_cast this
  omega

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

/-! ## Reading a magnitude -/

/-- The float for a significand `n ≤ 2^53` on the grid `2^k`: zero, the carry
    `2^52 · 2^(k+1)`, or `n · 2^k`. -/
def ofSig (s : Sign) (n : Nat) (k : Int) : UnpackedFloat :=
  if h : n = 0 then .zero s
  else if n = 2 ^ 53 then .finite s (2 ^ 52) (k + 1) (Nat.two_pow_pos 52)
  else .finite s n k (Nat.pos_of_ne_zero h)

/-- `read` on a sign and a magnitude: the body of `read`. -/
def readMag (s : Sign) (x : Rat) : UnpackedFloat :=
  if 2 ^ 1024 - 2 ^ 970 ≤ x then .infinity s
  else ofSig s (roundEven (x / 2 ^ gridExp x)).toNat (gridExp x)

theorem read_eq_readMag (d : Decimal) : read d = readMag d.sign (Rat.abs (Spec.toRat d)) := rfl

/-- The word the reader returns unpacks to what `read` computed. -/
theorem unpack_referenceBits (d : Decimal) : Spec.unpack (referenceBits d) = read d := by
  unfold referenceBits
  rw [toBits_pack]
  have hspec := read_spec d
  rcases lt_or_ge ((d.significand : Rat) * (10 : Rat) ^ d.exponent) (2 ^ 1024 - 2 ^ 970) with hd | hd
  · obtain ⟨hfin, -, hleg, -⟩ := hspec.1 hd
    generalize read d = u at *
    cases u with
    | notANumber => simp [UnpackedFloat.isFinite] at hfin
    | infinity s => simp [UnpackedFloat.isFinite] at hfin
    | zero s => exact unpack_pack_zero s
    | finite s n k hn => exact unpack_pack_finite s hn hleg
  · rw [hspec.2 hd]; exact unpack_pack_infinity _

/-! ## Extreme magnitudes -/

theorem threshold_pos : (0 : Rat) < (2 : Rat) ^ 1024 - 2 ^ 970 := by
  have h : (2 : Rat) ^ (970 : Int) < (2 : Rat) ^ (1024 : Int) := by
    have := zpow_le_zpow_right₀ (a := (2 : Rat)) (by decide) (show (970 : Int) ≤ 1023 by decide)
    have h2 := Rat.zpow_add_one (show (2 : Rat) ≠ 0 by decide) 1023
    rw [show (1023 : Int) + 1 = 1024 by decide] at h2
    rw [h2]
    have hpos := two_zpow_pos (1023 : Int)
    grind
  have h' : (2 : Rat) ^ (970 : Nat) < (2 : Rat) ^ (1024 : Nat) := h
  grind

theorem readMag_zero (s : Sign) : readMag s 0 = .zero s := by
  unfold readMag
  rw [if_neg (Rat.not_le.mpr threshold_pos), show roundEven (0 / (2 : Rat) ^ gridExp 0) = 0 by
    rw [Rat.div_def, Rat.zero_mul]
    exact roundEven_eq_of (n := 0) (by grind) (by grind) (fun h => absurd h (by grind))
      (fun h => absurd h (by grind))]
  rfl

theorem readMag_infinity (s : Sign) {x : Rat} (hx : (2 : Rat) ^ 1024 - 2 ^ 970 ≤ x) :
    readMag s x = .infinity s := by
  unfold readMag; rw [if_pos hx]

/-- `m · 10^e` overflows for `m ≥ 1` and `e ≥ 309`. -/
theorem overflow_of_big {m : Nat} (hm : m ≠ 0) {e : Int} (he : 308 < e) :
    (2 : Rat) ^ 1024 - 2 ^ 970 ≤ (m : Rat) * (10 : Rat) ^ e := by
  have h1 : (2 : Rat) ^ (1024 : Nat) ≤ (10 : Rat) ^ (309 : Nat) := by
    exact_mod_cast (show (2 : Nat) ^ 1024 ≤ 10 ^ 309 by decide +kernel)
  have h2 : (10 : Rat) ^ (309 : Nat) ≤ (10 : Rat) ^ e :=
    zpow_le_zpow_right₀ (a := 10) (by decide) (by omega : (309 : Int) ≤ e)
  have h3 : (1 : Rat) * (10 : Rat) ^ e ≤ (m : Rat) * (10 : Rat) ^ e :=
    Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm)
      (Rat.le_of_lt (ten_zpow_pos e))
  have h5 : (0 : Rat) < (2 : Rat) ^ (970 : Nat) := Rat.pow_pos (by decide)
  grind

end Srtfp.Reader
