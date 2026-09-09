module
/- Lean's model of binary64 (`Float.Model`, core since v4.33): the facts
   the proofs need. Packing a canonical unpacked float and unpacking it
   again gives it back; unpacking is injective away from NaN; the `(m, e)`
   of a finite word lie in the binary64 range (`Legal`). -/

public import Srtfp.Spec

@[expose] public section

namespace Srtfp.Model

open Float.Model Float.Model.UnpackedFloat

/-- The `(m, q)` a finite binary64 word unpacks to: `m < 2^53`,
    `-1074 ≤ q ≤ 971`, and only the subnormal exponent admits `m < 2^52`. -/
def Legal (m : Nat) (q : Int) : Prop :=
  m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ (q ≠ -1074 → 2 ^ 52 ≤ m)

theorem legal_zero : Legal 0 (-1074) := by unfold Legal; omega

/-! ## The three fields of a packed word -/

theorem Sign.ofBitVec_toBitVec (s : Sign) : Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

theorem Sign.toBitVec_ofBitVec (b : BitVec 1) : (Sign.ofBitVec b).toBitVec = b := by
  unfold Sign.ofBitVec
  split
  · rename_i h; rw [h]; rfl
  · rename_i h
    apply BitVec.eq_of_toNat_eq
    have := b.isLt
    have hne : b.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq h0)
    show 1 = b.toNat
    omega

/-- Or of the three disjoint fields is their sum. -/
theorem or_or_eq_add {s e m : Nat} (_hs : s < 2) (he : e < 2 ^ 11) (hm : m < 2 ^ 52) :
    (s <<< 11 ||| e) <<< 52 ||| m = s * 2 ^ 63 + e * 2 ^ 52 + m := by
  have h1 : s * 2 ^ 11 ||| e = s * 2 ^ 11 + e := by
    rw [Nat.mul_comm]; exact (Nat.two_pow_add_eq_or_of_lt he s).symm
  have h2 : (s * 2 ^ 11 + e) * 2 ^ 52 ||| m = (s * 2 ^ 11 + e) * 2 ^ 52 + m := by
    rw [Nat.mul_comm]; exact (Nat.two_pow_add_eq_or_of_lt hm _).symm
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, h1, h2]
  omega

theorem packComponents_toNat (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    (packComponents Format.binary64 s e m).toNat = s.toBitVec.toNat * 2 ^ 63 + e.toNat * 2 ^ 52 + m.toNat := by
  unfold packComponents
  rw [BitVec.toNat_append, BitVec.toNat_append]
  exact or_or_eq_add s.toBitVec.isLt e.isLt m.isLt

theorem unpackSign_packComponents (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    @unpackSign Format.binary64 (packComponents Format.binary64 s e m) = s.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  unfold unpackSign
  simp only [BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb'_toNat, packComponents_toNat,
    Nat.shiftRight_eq_div_pow]
  have := s.toBitVec.isLt; have := e.isLt; have := m.isLt
  show _ % 2 ^ 1 = _
  omega

theorem unpackExponent_packComponents (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    @unpackExponent Format.binary64 (packComponents Format.binary64 s e m) = e :=
  Float.Model.UnpackedFloat.unpackExponent_packComponents

theorem unpackMantissa_packComponents (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    @unpackMantissa Format.binary64 (packComponents Format.binary64 s e m) = m :=
  Float.Model.UnpackedFloat.unpackMantissa_packComponents

/-- Reassembling the three fields of a word gives the word back. -/
theorem packComponents_unpack (b : BitVec 64) :
    packComponents Format.binary64 (Sign.ofBitVec (@unpackSign Format.binary64 b))
      (@unpackExponent Format.binary64 b) (@unpackMantissa Format.binary64 b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [packComponents_toNat, Sign.toBitVec_ofBitVec]
  unfold unpackSign unpackExponent unpackMantissa
  simp only [BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hb := b.isLt
  omega

/-! ## `unpack` of a packed word -/

theorem exponentBias_eq : Format.binary64.exponentBias = 1023 := rfl

/-- `unpack` of `packComponents`, by cases on the fields. -/
theorem unpack_packComponents (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    UnpackedFloat.unpack Format.binary64 (packComponents Format.binary64 s e m) =
      if e.toNat = 2047 then (if m.toNat = 0 then .infinity s else .notANumber)
      else if e.toNat = 0 then
        (if h : m.toNat = 0 then .zero s else .finite s m.toNat (-1074) (Nat.pos_of_ne_zero h))
      else .finite s (m.toNat + 2 ^ 52) ((e.toNat : Int) - 1075) (by omega) := by
  unfold UnpackedFloat.unpack
  simp only [unpackSign_packComponents, unpackExponent_packComponents, unpackMantissa_packComponents,
    Sign.ofBitVec_toBitVec, exponentBias_eq]
  have hE : (e = -1#11) ↔ e.toNat = 2047 := by rw [BitVec.toNat_eq]; rfl
  have hZ : (e = 0#11) ↔ e.toNat = 0 := by rw [BitVec.toNat_eq]; rfl
  have hM : (m = 0#52) ↔ m.toNat = 0 := by rw [BitVec.toNat_eq]; rfl
  have hcat : ((1#1 : BitVec 1) ++ m).toNat = m.toNat + 2 ^ 52 := by
    have h2 := Nat.two_pow_add_eq_or_of_lt m.isLt 1
    rw [Nat.mul_one] at h2
    rw [BitVec.toNat_append]
    show 1 <<< 52 ||| _ = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, ← h2]
    omega
  simp only [hE, hZ, hM, hcat]
  by_cases h1 : e.toNat = 2047 <;> by_cases h2 : e.toNat = 0 <;> simp [h1, h2] <;> omega

/-! ## `unpack ∘ pack` on canonical unpacked floats -/

/-- The format's constants, for `omega`. -/
theorem binary64_facts :
    2 ^ Format.binary64.exponentBits = 2048 ∧ 2 ^ Format.binary64.mantissaBitsWithoutImplicit = 2 ^ 52
    ∧ Format.binary64.exponentBias = 1023 ∧ Format.binary64.mantissaBitsWithoutImplicit = 52
    ∧ Format.binary64.mantissaBits = 53 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem unpack_pack_infinity (s : Sign) :
    UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 (.infinity s)) = .infinity s := by
  show UnpackedFloat.unpack Format.binary64 (packComponents Format.binary64 s (-1#_) 0) = _
  rw [unpack_packComponents]; rfl

theorem unpack_pack_zero (s : Sign) :
    UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 (.zero s)) = .zero s := by
  show UnpackedFloat.unpack Format.binary64 (packComponents Format.binary64 s 0 0) = _
  rw [unpack_packComponents]; rfl

/-- `pack` of a legal finite float: the biased exponent, `0` for a
    subnormal, and the low 52 bits of the significand. -/
theorem pack_finite (s : Sign) {n : Nat} {k : Int} (hn : 0 < n) (h : Legal n k) :
    UnpackedFloat.pack Format.binary64 (.finite s n k hn)
      = packComponents Format.binary64 s (BitVec.ofNat _ (if n < 2 ^ 52 then 0 else (k + 1075).toNat))
          (BitVec.ofNat _ n) := by
  obtain ⟨h53, hk0, hk1, hnorm⟩ := h
  obtain ⟨hA, hB, hC, hD, hMB⟩ := binary64_facts
  have hlog : n.log2 = 52 ↔ ¬ n < 2 ^ 52 := by rw [Nat.log2_eq_iff (by omega)]; omega
  unfold UnpackedFloat.pack
  simp only
  rw [if_neg (by omega)]
  split
  · rw [if_neg (hlog.mp (by omega)),
      show (k + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat
        = (k + 1075).toNat by omega]
  · rw [if_pos (by have := hlog.mpr; omega)]

theorem unpack_pack_finite (s : Sign) {n : Nat} {k : Int} (hn : 0 < n) (h : Legal n k) :
    UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 (.finite s n k hn))
      = .finite s n k hn := by
  obtain ⟨h53, hk0, hk1, hnorm⟩ := h
  rw [pack_finite s hn ⟨h53, hk0, hk1, hnorm⟩, unpack_packComponents]
  simp only [BitVec.toNat_ofNat]
  by_cases hlt : n < 2 ^ 52
  · -- subnormal: `k = -1074`
    rw [if_pos hlt, if_neg (by omega), if_pos (by omega), dif_neg (by omega)]
    simp only [UnpackedFloat.finite.injEq, true_and]; omega
  · -- normal
    rw [if_neg hlt, if_neg (by omega), if_neg (by omega)]
    simp only [UnpackedFloat.finite.injEq, true_and]; omega

/-! ## The bounds of a finite word -/

theorem legal_of_unpack {b : BitVec 64} {s : Sign} {n : Nat} {k : Int} {h : 0 < n}
    (hu : UnpackedFloat.unpack Format.binary64 b = .finite s n k h) : Legal n k := by
  rw [← packComponents_unpack b, unpack_packComponents] at hu
  have hE := (@unpackExponent Format.binary64 b).isLt
  have hM := (@unpackMantissa Format.binary64 b).isLt
  obtain ⟨hA, hB, hC, hD, hMB⟩ := binary64_facts
  unfold Legal
  split at hu
  · split at hu <;> cases hu
  · split at hu
    · split at hu
      · cases hu
      · simp only [UnpackedFloat.finite.injEq] at hu
        omega
    · simp only [UnpackedFloat.finite.injEq] at hu
      omega

/-! ## `pack ∘ unpack`, and injectivity -/

theorem pack_unpack_packComponents (s : Sign) (e : BitVec 11) (m : BitVec 52)
    (h : Format.Valid Format.binary64 (packComponents Format.binary64 s e m)) :
    UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 (packComponents Format.binary64 s e m))
      = packComponents Format.binary64 s e m := by
  have hElt := e.isLt
  have hMlt := m.isLt
  rw [unpack_packComponents]
  split
  · rename_i hE
    split
    · rename_i hM
      show packComponents Format.binary64 s (-1#_) 0 = _
      apply BitVec.eq_of_toNat_eq
      rw [packComponents_toNat, packComponents_toNat, hE, hM]; rfl
    · rename_i hM
      show packedNaN Format.binary64 = _
      refine (h.eq_packedNaN ?_ ?_).symm
      · rw [unpackExponent_packComponents]; exact BitVec.eq_of_toNat_eq (by rw [hE]; rfl)
      · rw [unpackMantissa_packComponents]
        intro h0; apply hM; rw [h0]; rfl
  · rename_i hE
    split
    · rename_i hZ
      split
      · rename_i hM
        show packComponents Format.binary64 s 0 0 = _
        apply BitVec.eq_of_toNat_eq
        rw [packComponents_toNat, packComponents_toNat, hZ, hM]; rfl
      · rw [pack_finite s _ ⟨by omega, by omega, by decide, fun h => absurd rfl h⟩, if_pos hMlt]
        apply BitVec.eq_of_toNat_eq
        rw [packComponents_toNat, packComponents_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    · rename_i hZ
      rw [pack_finite s _ ⟨by omega, by omega, by omega, fun _ => by omega⟩, if_neg (by omega)]
      apply BitVec.eq_of_toNat_eq
      rw [packComponents_toNat, packComponents_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- `pack ∘ unpack` is the identity on words that are not a NaN (other
    than the canonical one). -/
theorem pack_unpack (b : BitVec 64) (h : Format.Valid Format.binary64 b) :
    UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 b) = b := by
  have hfields := packComponents_unpack b
  rw [← hfields] at h ⊢
  exact pack_unpack_packComponents _ _ _ h

/-- A word that does not unpack to NaN is valid. -/
theorem valid_of_ne_nan {b : BitVec 64} (h : UnpackedFloat.unpack Format.binary64 b ≠ .notANumber) :
    Format.Valid Format.binary64 b where
  eq_packedNaN hE hM := by
    exfalso; apply h
    unfold UnpackedFloat.unpack
    simp only [hE, hM, if_true, if_false]

/-- `unpack` is injective away from NaN. -/
theorem unpack_inj {b b' : BitVec 64} (h : UnpackedFloat.unpack Format.binary64 b ≠ .notANumber)
    (he : UnpackedFloat.unpack Format.binary64 b = UnpackedFloat.unpack Format.binary64 b') : b = b' := by
  rw [← pack_unpack b (valid_of_ne_nan h), ← pack_unpack b' (valid_of_ne_nan (he ▸ h)), he]

/-! ## On words -/

theorem toBits_pack (u : UnpackedFloat) :
    Spec.unpack (Float.Model.pack u).toBits = UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 u) := by
  unfold Spec.unpack Float.Model.pack
  simp

theorem word_inj {w w' : UInt64} (h : Spec.unpack w ≠ .notANumber) (he : Spec.unpack w = Spec.unpack w') :
    w = w' :=
  UInt64.toBitVec_inj.mp (unpack_inj h he)

/-- `Float.Model.ofBits` is the identity on words that are not a NaN. -/
theorem toBits_ofBits (x : UInt64) (h : Spec.unpack x ≠ .notANumber) :
    (Float.Model.ofBits x).toBits = x := by
  show UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (UnpackedFloat.unpack Format.binary64 x.toBitVec)) = x
  rw [pack_unpack _ (valid_of_ne_nan h)]

/-- Two models with the same word are equal. -/
theorem model_ext {a b : Float.Model} (h : a.toBits = b.toBits) : a = b := by
  cases a; cases b; cases h; rfl

end Srtfp.Model
