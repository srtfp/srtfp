module
/- The reader lands in the rounding interval. For a magnitude below the
   overflow threshold, `decimalToFloatBits` returns a finite word of the
   decimal's sign whose interval `R_w` contains the magnitude; at or past
   the threshold it returns the infinity of that sign. Read off the
   branches of the definition in `Srtfp/Clinger.lean`. -/
public import Srtfp.Proofs.Reader.Round
public import Srtfp.Proofs.Reader.Words

@[expose] public section

open Srtfp.Compat

namespace Srtfp.Clinger

open Srtfp.Float Srtfp.Printer

/-! ## The overflow threshold -/

theorem two_pow_eq_zpow (n : Nat) : (2 : ℚ) ^ n = (2 : ℚ) ^ (n : Int) := (Rat.zpow_natCast _ _).symm

/-- `2^1024 - 2^970 = (2^53 - 1/2) · 2^971`: the midpoint between the largest
finite value and its would-be successor. -/
theorem threshold_eq : (2 : ℚ) ^ 1024 - 2 ^ 970 = (2 ^ 53 - 1/2) * (2 : ℚ) ^ (971 : Int) := by
  rw [two_pow_eq_zpow 1024, two_pow_eq_zpow 970, show ((1024 : Nat) : Int) = 53 + 971 by decide,
    Rat.zpow_add (by decide), ← Rat.zpow_natCast,
    show (2 : ℚ) ^ (971 : Int) = 2 ^ (((970 : Nat) : Int)) * 2 by
      rw [← Rat.zpow_add_one (by decide)]; rfl]
  generalize (2 : ℚ) ^ (((970 : Nat) : Int)) = P
  grind

theorem threshold_pos : (0 : ℚ) < 2 ^ 1024 - 2 ^ 970 := by
  rw [threshold_eq]
  exact Rat.mul_pos (by grind) (two_zpow_pos _)

/-- `2^1023 ≤` the threshold. -/
theorem two_zpow_1023_le : (2 : ℚ) ^ (1023 : Int) ≤ 2 ^ 1024 - 2 ^ 970 := by
  rw [threshold_eq, show (1023 : Int) = 52 + 971 by decide, Rat.zpow_add (by decide),
    ← Rat.zpow_natCast]
  have := two_zpow_pos (971 : Int)
  exact Rat.mul_le_mul_of_nonneg_right (by grind) (le_of_lt this)

/-! ## Membership in `R_v` from the rounding -/

/-- The nearest-integer conditions on `t` put `t · 2^k` in `R_{n·2^k}`; at the
bottom of a binade the interval is narrower on the left, so there `t ≥ n`
is required. -/
theorem InRv_of_round {n : Nat} {k : Int} {t : ℚ}
    (hl : (n : ℚ) - 1/2 ≤ t) (hr : t ≤ n + 1/2)
    (hl' : t = n - 1/2 → n % 2 = 0) (hr' : t = n + 1/2 → n % 2 = 0)
    (hirr : n = 2 ^ 52 ∧ k > -1074 → (n : ℚ) ≤ t) :
    InRv n k (t * (2 : ℚ) ^ k) = true := by
  have hp := two_zpow_pos k
  have h1 := Rat.mul_le_mul_of_nonneg_right hl (le_of_lt hp)
  have h2 := Rat.mul_le_mul_of_nonneg_right hr (le_of_lt hp)
  unfold InRv vl vr
  by_cases he : n % 2 = 0
  · rw [if_pos he]
    simp only [decide_eq_true_eq]
    split
    · have h3 := Rat.mul_le_mul_of_nonneg_right (hirr ‹_›) (le_of_lt hp)
      generalize (2 : ℚ) ^ k = p at *
      grind
    · exact ⟨h1, h2⟩
  · rw [if_neg he]
    simp only [decide_eq_true_eq]
    have hl2 : (n : ℚ) - 1/2 < t := lt_of_le_of_ne hl (fun h => he (hl' h.symm))
    have hr2 : t < n + 1/2 := lt_of_le_of_ne hr (fun h => he (hr' h))
    have h3 := Rat.mul_lt_mul_of_pos_right hl2 hp
    have h4 := Rat.mul_lt_mul_of_pos_right hr2 hp
    split
    · exfalso; exact he (by rw [‹n = 2 ^ 52 ∧ k > -1074›.1])
    · exact ⟨h3, h4⟩

/-! ## The words the reader packs -/

theorem normal_pack (sign : Bool) {e : Int} (he : -1022 ≤ e ∧ e ≤ 1023) {n : Nat}
    (hn : 2 ^ 52 ≤ n ∧ n < 2 ^ 53) :
    Word.isFinite (Word.pack sign (e + 1023).toNat (n - 2 ^ 52)) = true
    ∧ Word.decode (Word.pack sign (e + 1023).toNat (n - 2 ^ 52)) = ⟨sign, n, e - 52⟩ := by
  have hbe : (e + 1023).toNat < 2047 := by omega
  have hm : n - 2 ^ 52 < 2 ^ 52 := by omega
  refine ⟨isFinite_pack sign hbe hm, ?_⟩
  rw [decode_pack sign (by omega) hm, if_neg (by omega)]
  simp only [Decoded.mk.injEq, true_and]
  omega

theorem subnormal_pack (sign : Bool) {n : Nat} (hn : n < 2 ^ 52) :
    Word.isFinite (Word.pack sign 0 n) = true
    ∧ Word.decode (Word.pack sign 0 n) = ⟨sign, n, -1074⟩ := by
  refine ⟨isFinite_pack sign (by decide) hn, ?_⟩
  rw [decode_pack sign (by decide) hn, if_pos rfl]

theorem min_normal_pack (sign : Bool) :
    Word.isFinite (Word.pack sign 1 0) = true
    ∧ Word.decode (Word.pack sign 1 0) = ⟨sign, 2 ^ 52, -1074⟩ := by
  refine ⟨isFinite_pack sign (by decide) (by decide), ?_⟩
  rw [decode_pack sign (by decide) (by decide), if_neg (by decide)]
  simp only [Decoded.mk.injEq, true_and, Nat.zero_add]
  decide

/-! ## Scaling and rounding -/

/-- Scale `x = a / b` by `2^j` and round: `n` is the nearest integer to
`t = x · 2^j`, ties to even, and `x = t · 2^(-j)`. -/
theorem scale_round {a b : Nat} (hb : 0 < b) {x : ℚ} (hab : (a : ℚ) = x * b) (j : Int) :
    let t := x * (2 : ℚ) ^ j
    let nd := scaleByPow2 a b j
    let n := roundNearestEven nd.1 nd.2
    x = t * (2 : ℚ) ^ (-j) ∧ 0 < nd.2 ∧ (nd.1 : ℚ) / nd.2 = t
    ∧ (n : ℚ) - 1/2 ≤ t ∧ t ≤ n + 1/2 ∧ (t = n - 1/2 → n % 2 = 0) ∧ (t = n + 1/2 → n % 2 = 0) := by
  intro t nd n
  obtain ⟨hden, hscale⟩ := scaleByPow2_spec hb j
  have hbq : (b : ℚ) ≠ 0 := by have : (0 : ℚ) < b := by exact_mod_cast hb
                               grind
  have ht : (nd.1 : ℚ) / nd.2 = t := by rw [hscale, hab, Rat.mul_div_cancel hbq]
  obtain ⟨hl, hr, hl', hr'⟩ := roundNearestEven_spec (num := nd.1) hden
  rw [ht] at hl hr hl' hr'
  exact ⟨by show x = x * _ * _; rw [Rat.mul_assoc, two_zpow_mul_neg, Rat.mul_one], hden, ht,
    hl, hr, hl', hr'⟩

/-- Below `2^1023` is below the threshold. -/
theorem lt_threshold_of_lt {x : ℚ} {e : Int} (hx : x < (2 : ℚ) ^ (e + 1)) (he : e + 1 ≤ 1023) :
    x < 2 ^ 1024 - 2 ^ 970 :=
  lt_of_lt_of_le hx (le_trans (zpow_le_zpow_right₀ (by decide) he) two_zpow_1023_le)

/-! ## The fraction `a / b` -/

/-- The reader's fraction for `sig · 10^exp`. -/
theorem fraction_spec {sig : Nat} (hsig : sig ≠ 0) (exp : Int) :
    let ab : Nat × Nat := if exp ≥ 0 then (sig * 10 ^ exp.toNat, 1) else (sig, 10 ^ (-exp).toNat)
    0 < ab.1 ∧ 0 < ab.2 ∧ (ab.1 : ℚ) = (sig : ℚ) * (10 : ℚ) ^ exp * ab.2 := by
  intro ab
  have hs : 0 < sig := Nat.pos_of_ne_zero hsig
  by_cases he : exp ≥ 0
  · simp only [ab, if_pos he]
    refine ⟨Nat.mul_pos hs (Nat.pow_pos (by decide)), by decide, ?_⟩
    have : (10 : ℚ) ^ exp = (10 : ℚ) ^ exp.toNat := by
      conv => lhs; rw [← Int.toNat_of_nonneg he]
      exact Rat.zpow_natCast _ _
    rw [this]; push_cast; rw [Rat.mul_one]
  · simp only [ab, if_neg he]
    refine ⟨hs, Nat.pow_pos (by decide), ?_⟩
    have hN : (10 : ℚ) ^ (-exp) = (10 : ℚ) ^ (-exp).toNat := by
      conv => lhs; rw [← Int.toNat_of_nonneg (by omega : 0 ≤ -exp)]
      exact Rat.zpow_natCast _ _
    have hcancel : (10 : ℚ) ^ exp * (10 : ℚ) ^ (-exp) = 1 := by
      rw [← Rat.zpow_add (by decide), show exp + -exp = 0 by omega, Rat.zpow_zero]
    push_cast
    rw [← hN, Rat.mul_assoc, hcancel, Rat.mul_one]

/-! ## The reader -/

/-- **The reader lands in `R_w`.** Below the threshold, `decimalToFloatBits`
returns a finite word of the given sign whose interval contains
`sig · 10^exp`; at or past it, the infinity of that sign. -/
theorem decimalToFloatBits_spec (sign : Bool) (sig : Nat) (exp : Int) :
    ((sig : ℚ) * (10 : ℚ) ^ exp < 2 ^ 1024 - 2 ^ 970 →
        Word.isFinite (decimalToFloatBits sign sig exp) = true
        ∧ (Word.decode (decimalToFloatBits sign sig exp)).sign = sign
        ∧ InRv (Word.decode (decimalToFloatBits sign sig exp)).m
            (Word.decode (decimalToFloatBits sign sig exp)).q ((sig : ℚ) * (10 : ℚ) ^ exp) = true)
    ∧ (2 ^ 1024 - 2 ^ 970 ≤ (sig : ℚ) * (10 : ℚ) ^ exp →
        decimalToFloatBits sign sig exp = Word.pack sign 2047 0) := by
  generalize hx : (sig : ℚ) * (10 : ℚ) ^ exp = x
  have hthr := threshold_pos
  unfold decimalToFloatBits
  by_cases hsig : sig = 0
  · -- zero reads to the zero word, and `0 ∈ R_0`
    subst hsig
    rw [if_pos rfl]
    have hx0 : x = 0 := by rw [← hx]; simp
    subst hx0
    obtain ⟨hfin, hdec⟩ := subnormal_pack sign (n := 0) (by decide)
    refine ⟨fun _ => ⟨hfin, ?_, ?_⟩, fun h => absurd h (Rat.not_le.mpr hthr)⟩
    · show (Word.decode (Word.pack sign 0 0)).sign = sign
      rw [hdec]
    · show InRv (Word.decode (Word.pack sign 0 0)).m (Word.decode (Word.pack sign 0 0)).q 0 = true
      rw [hdec]
      have := InRv_of_round (n := 0) (k := -1074) (t := 0) (by grind) (by grind)
        (fun _ => rfl) (fun _ => rfl) (fun h => absurd h.1 (by decide))
      rwa [Rat.zero_mul] at this
  rw [if_neg hsig]
  -- the fraction `a / b = x`
  obtain ⟨ha, hb, hab⟩ := fraction_spec hsig exp
  rw [hx] at hab
  generalize (if exp ≥ 0 then (sig * 10 ^ exp.toNat, 1) else (sig, 10 ^ (-exp).toNat) : Nat × Nat) = ab
    at ha hb hab ⊢
  obtain ⟨a, b⟩ := ab
  simp only at ha hb hab ⊢
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  -- the binary exponent: `2^e ≤ x < 2^(e+1)`
  obtain ⟨he1, he2⟩ := findBinaryExp_spec ha hb
  generalize findBinaryExp a b = e at he1 he2 ⊢
  rw [hab] at he1 he2
  have hxl : (2 : ℚ) ^ e ≤ x := Rat.le_of_mul_le_mul_right he1 hbq
  have hxr : x < (2 : ℚ) ^ (e + 1) := Rat.lt_of_mul_lt_mul_right he2 (le_of_lt hbq)
  have hxpos : 0 < x := lt_of_lt_of_le (two_zpow_pos e) hxl
  by_cases hover : e > 1023
  · -- `x ≥ 2^1024`: overflow
    rw [if_pos hover]
    have h1 : (2 : ℚ) ^ ((1024 : Nat) : Int) ≤ 2 ^ e := zpow_le_zpow_right₀ (by decide) (by omega)
    have h2 : (2 : ℚ) ^ 1024 - 2 ^ 970 ≤ (2 : ℚ) ^ ((1024 : Nat) : Int) := by
      rw [← two_pow_eq_zpow]
      have := Rat.pow_pos (a := (2 : ℚ)) (n := 970) (by decide)
      grind
    exact ⟨fun h => absurd h (Rat.not_lt.mpr (le_trans h2 (le_trans h1 hxl))), fun _ => rfl⟩
  rw [if_neg hover]
  by_cases hnorm : e ≥ -1022
  · -- normal binade: round `x / 2^(e-52)` to an integer in `[2^52, 2^53]`
    rw [if_pos hnorm]
    obtain ⟨hxt, hden, ht, hl, hr, hl', hr'⟩ := scale_round hb hab (52 - e)
    generalize scaleByPow2 a b (52 - e) = nd at *
    obtain ⟨num, denom⟩ := nd
    try simp only at hden ht hl hr hl' hr' ⊢
    rw [show -(52 - e) = e - 52 by omega] at hxt
    have hp := two_zpow_pos (52 - e)
    have hp' := two_zpow_pos (e - 52)
    -- `2^52 ≤ t < 2^53`
    have htl : ((2 ^ 52 : Nat) : ℚ) ≤ x * (2 : ℚ) ^ (52 - e) := by
      rw [← two_zpow_natCast, show ((52 : Nat) : Int) = e + (52 - e) by omega, Rat.zpow_add (by decide)]
      exact Rat.mul_le_mul_of_nonneg_right hxl (le_of_lt hp)
    have htr : x * (2 : ℚ) ^ (52 - e) < ((2 ^ 53 : Nat) : ℚ) := by
      rw [← two_zpow_natCast, show ((53 : Nat) : Int) = (e + 1) + (52 - e) by omega, Rat.zpow_add (by decide)]
      exact Rat.mul_lt_mul_of_pos_right hxr hp
    obtain ⟨hml, hmr⟩ := roundNearestEven_bounds hden (by rw [ht]; exact htl) (by rw [ht]; exact htr)
    generalize roundNearestEven num denom = n at hl hr hl' hr' hml hmr ⊢
    generalize x * (2 : ℚ) ^ (52 - e) = t at hl hr hl' hr' htl htr hxt
    have htr' : t < (2 : ℚ) ^ 53 := by rw [two_pow_eq_zpow, two_zpow_natCast]; exact htr
    by_cases hcarry : n ≥ 2 ^ 53
    · -- rounded up to `2^53`: the next binade
      rw [if_pos hcarry]
      have hn : n = 2 ^ 53 := by omega
      subst hn
      push_cast at hl hr hl' hr'
      by_cases hover' : e + 1 > 1023
      · rw [if_pos hover']
        have he : e = 1023 := by omega
        subst he
        -- `x ≥ (2^53 - 1/2) · 2^971`: the threshold
        have : (2 ^ 53 - 1/2 : ℚ) * (2 : ℚ) ^ (971 : Int) ≤ x := by
          rw [hxt, show (1023 : Int) - 52 = 971 by decide]
          exact Rat.mul_le_mul_of_nonneg_right hl (le_of_lt (two_zpow_pos _))
        rw [← threshold_eq] at this
        exact ⟨fun h => absurd h (Rat.not_lt.mpr this), fun _ => rfl⟩
      · rw [if_neg hover']
        obtain ⟨hfin, hdec⟩ := normal_pack sign (e := e + 1) (by omega) (n := 2 ^ 52) (by decide)
        have hmem : InRv (2 ^ 52) (e + 1 - 52) x = true := by
          have h2 : (2 : ℚ) ^ (e + 1 - 52) = 2 ^ (e - 52) * 2 := by
            rw [← Rat.zpow_add_one (by decide), show e - 52 + 1 = e + 1 - 52 by omega]
          unfold InRv vl vr
          rw [if_pos (by decide), if_pos ⟨rfl, by omega⟩, h2]
          simp only [decide_eq_true_eq]
          push_cast
          have h3 := Rat.mul_le_mul_of_nonneg_right hl (le_of_lt hp')
          have h4 := Rat.mul_lt_mul_of_pos_right htr' hp'
          generalize (2 : ℚ) ^ (e - 52) = p at *
          rw [hxt]
          constructor <;> grind
        exact ⟨fun _ => ⟨hfin, by rw [hdec], by rw [hdec]; exact hmem⟩,
          fun h => absurd (lt_threshold_of_lt hxr (by omega)) (Rat.not_lt.mpr h)⟩
    · -- `2^52 ≤ n < 2^53`: the word `(n, e - 52)`
      rw [if_neg hcarry]
      obtain ⟨hfin, hdec⟩ := normal_pack sign (e := e) (by omega) (n := n) (by omega)
      have hmem : InRv n (e - 52) x = true := by
        rw [hxt]
        exact InRv_of_round hl hr hl' hr' (fun h => by rw [h.1]; exact htl)
      refine ⟨fun _ => ⟨hfin, by rw [hdec], by rw [hdec]; exact hmem⟩, fun h => absurd ?_ (Rat.not_lt.mpr h)⟩
      rcases Int.lt_or_le e 1023 with hlt | hge
      · exact lt_threshold_of_lt hxr (by omega)
      -- `e = 1023`: `x ≤ (n + 1/2) · 2^971 ≤ (2^53 - 1/2) · 2^971`, strictly, since the
      -- endpoint `t = 2^53 - 1/2` would have rounded to the even `2^53`
      have he : e = 1023 := by omega
      subst he
      rw [show (1023 : Int) - 52 = 971 by decide] at hxt hp'
      have hn' : (n : ℚ) + 1 ≤ 2 ^ 53 := by exact_mod_cast (show n + 1 ≤ 2 ^ 53 by omega)
      have hxup : x ≤ (2 ^ 53 - 1/2) * (2 : ℚ) ^ (971 : Int) := by
        rw [hxt]; exact Rat.mul_le_mul_of_nonneg_right (by grind) (le_of_lt hp')
      rw [threshold_eq]
      refine lt_of_le_of_ne hxup fun heq' => ?_
      have : t = 2 ^ 53 - 1/2 := by
        rw [hxt] at heq'
        exact (mul_left_inj' (by grind)).mp heq'
      have h6 := hr' (by grind)
      have h8 : n + 1 = 2 ^ 53 := by exact_mod_cast (show (n : ℚ) + 1 = 2 ^ 53 by grind)
      omega
  · -- subnormal: round `x · 2^1074` to an integer in `[0, 2^52]`
    rw [if_neg hnorm]
    obtain ⟨hxt, hden, ht, hl, hr, hl', hr'⟩ := scale_round hb hab 1074
    generalize scaleByPow2 a b 1074 = nd at *
    obtain ⟨num, denom⟩ := nd
    try simp only at hden ht hl hr hl' hr' ⊢
    have hp := two_zpow_pos (1074 : Int)
    have htl : ((0 : Nat) : ℚ) ≤ x * (2 : ℚ) ^ (1074 : Int) := by
      have h0 : (0 : ℚ) ≤ x * (2 : ℚ) ^ (1074 : Int) := Rat.mul_nonneg (le_of_lt hxpos) (le_of_lt hp)
      generalize x * (2 : ℚ) ^ (1074 : Int) = y at h0 ⊢
      exact_mod_cast h0
    have htr : x * (2 : ℚ) ^ (1074 : Int) < ((2 ^ 52 : Nat) : ℚ) := by
      rw [← two_zpow_natCast, show ((52 : Nat) : Int) = -1022 + 1074 by decide, Rat.zpow_add (by decide)]
      have : (2 : ℚ) ^ (e + 1) ≤ (2 : ℚ) ^ (-1022 : Int) := zpow_le_zpow_right₀ (by decide) (by omega)
      exact Rat.mul_lt_mul_of_pos_right (lt_of_lt_of_le hxr this) hp
    obtain ⟨-, hmr⟩ := roundNearestEven_bounds hden (by rw [ht]; exact htl) (by rw [ht]; exact htr)
    generalize roundNearestEven num denom = n at hl hr hl' hr' hmr ⊢
    generalize x * (2 : ℚ) ^ (1074 : Int) = t at hl hr hl' hr' htl htr hxt
    have hmem : InRv n (-1074) x = true := by
      rw [hxt]
      exact InRv_of_round hl hr hl' hr' (fun h => absurd h.2 (by decide))
    refine ⟨fun _ => ?_, fun h => absurd (lt_threshold_of_lt hxr (by omega)) (Rat.not_lt.mpr h)⟩
    by_cases hz : n = 0
    · rw [if_pos hz]
      unfold zeroWord
      obtain ⟨hfin, hdec⟩ := subnormal_pack sign (n := 0) (by decide)
      exact ⟨hfin, by rw [hdec], by rw [hdec, ← hz]; exact hmem⟩
    · rw [if_neg hz]
      by_cases hmin : n ≥ 2 ^ 52
      · rw [if_pos hmin]
        have hn : n = 2 ^ 52 := by omega
        subst hn
        obtain ⟨hfin, hdec⟩ := min_normal_pack sign
        rw [show 2 ^ 52 - 2 ^ 52 = 0 by decide]
        exact ⟨hfin, by rw [hdec], by rw [hdec]; exact hmem⟩
      · rw [if_neg hmin]
        obtain ⟨hfin, hdec⟩ := subnormal_pack sign (n := n) (by omega)
        exact ⟨hfin, by rw [hdec], by rw [hdec]; exact hmem⟩

end Srtfp.Clinger
