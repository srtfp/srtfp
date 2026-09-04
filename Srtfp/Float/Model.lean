module
/- The bit round-trip of Lean's `Float.Model` (core, since v4.33):
   `Float.Model.ofBits` is the identity on valid words, so
   `(Float.ofBits x).toBits = x` for every non-NaN `x` — the statement of
   the runtime axiom in `Srtfp/Float/RuntimeAxiom.lean`, as a theorem.

   In v4.33 `Float` is a structure around `Float.Model` and `Float.ofBits`,
   `Float.toBits` are definitions over it (`@[extern]` only attaches the
   runtime implementation), so the round-trip needs no axiom: what remains
   trusted is the compiler's `@[extern]` contract, as for every primitive.

   This module needs Lean ≥ v4.33 (`Init.Data.Float.Model`) and is built by
   the opt-in library `SrtfpModel` only; the pinned toolchain cannot import
   it. Raising the toolchain floor would let it replace the axiom. -/

public import Init.Data.Float

@[expose] public section

namespace Float.Model

open UnpackedFloat

theorem Sign.toBitVec_ofBitVec (sv : BitVec 1) : (Sign.ofBitVec sv).toBitVec = sv := by
  unfold Sign.ofBitVec
  split
  · rename_i h; rw [h]; rfl
  · rename_i h
    apply BitVec.eq_of_toNat_eq
    have := sv.isLt
    have hne : sv.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq h0)
    show 1 = sv.toNat
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

/-- Reassembling the three fields of a binary64 word gives the word back. -/
theorem packComponents_unpack (b : BitVec 64) :
    packComponents Format.binary64 (Sign.ofBitVec (@unpackSign Format.binary64 b))
      (@unpackExponent Format.binary64 b) (@unpackMantissa Format.binary64 b) = b := by
  unfold packComponents
  rw [Sign.toBitVec_ofBitVec]
  apply BitVec.eq_of_toNat_eq
  unfold unpackSign unpackExponent unpackMantissa
  simp only [BitVec.toNat_append, BitVec.toNat_cast, BitVec.extractLsb, BitVec.extractLsb'_toNat]
  show ((b.toNat >>> 63 % 2 ^ 1) <<< 11 ||| b.toNat >>> 52 % 2 ^ 11) <<< 52 ||| b.toNat >>> 0 % 2 ^ 52
    = b.toNat
  have hb := b.isLt
  have hs : b.toNat >>> 63 % 2 ^ 1 < 2 := Nat.mod_lt _ (by decide)
  have he : b.toNat >>> 52 % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by decide)
  have hm : b.toNat >>> 0 % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  rw [or_or_eq_add hs he hm]
  omega

theorem ext {f g : Float.Model} (h : f.toBits = g.toBits) : f = g := by
  cases f; cases g; cases h; rfl

/-- `pack ∘ unpack` is the identity on valid binary64 words. -/
theorem pack_unpack (b : BitVec 64) (h : Format.Valid Format.binary64 b) :
    UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 b) = b := by
  have hfields := packComponents_unpack b
  have hbias : Format.binary64.exponentBias = 1023 := rfl
  have hmb : Format.binary64.mantissaBits = 53 := rfl
  have hElt : (@unpackExponent Format.binary64 b).toNat < 2 ^ 11 := (@unpackExponent Format.binary64 b).isLt
  have hMlt : (@unpackMantissa Format.binary64 b).toNat < 2 ^ 52 := (@unpackMantissa Format.binary64 b).isLt
  unfold UnpackedFloat.unpack
  simp only
  by_cases hE : @unpackExponent Format.binary64 b = -1#_
  · rw [if_pos hE]
    by_cases hM : @unpackMantissa Format.binary64 b = 0#_
    · rw [if_pos hM]
      show packedInfinity Format.binary64 _ = b
      rw [hE, hM] at hfields
      exact hfields
    · rw [if_neg hM]
      show packedNaN Format.binary64 = b
      exact (h.eq_packedNaN hE hM).symm
  · rw [if_neg hE]
    have hne : (@unpackExponent Format.binary64 b).toNat ≠ 2047 := by
      intro heq; apply hE
      apply BitVec.eq_of_toNat_eq
      rw [heq]; rfl
    by_cases hZ : @unpackExponent Format.binary64 b = 0#_
    · rw [if_pos hZ]
      split
      · rename_i hM
        show packedZero Format.binary64 _ = b
        rw [hZ, hM] at hfields
        exact hfields
      · rename_i hM
        -- subnormal: `m < 2^52`, exponent `-1074`
        show UnpackedFloat.pack Format.binary64 (.finite _ _ _ _) = b
        unfold UnpackedFloat.pack
        simp only
        have hmpos : 0 < (@unpackMantissa Format.binary64 b).toNat := by
          rcases Nat.eq_zero_or_pos (@unpackMantissa Format.binary64 b).toNat with h0 | h0
          · exact absurd (BitVec.eq_of_toNat_eq h0) hM
          · exact h0
        have hlog : (@unpackMantissa Format.binary64 b).toNat.log2 < 52 :=
          (Nat.log2_lt (by omega)).mpr hMlt
        have h0 : (@unpackExponent Format.binary64 b).toNat = 0 := by rw [hZ]; rfl
        rw [hbias, hmb, h0]
        split
        · omega
        · split
          · omega
          · rw [hZ] at hfields
            refine Eq.trans ?_ hfields
            congr 1
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat]
            omega
    · rw [if_neg hZ]
      -- normal: `m = 2^52 + mantissa`, `log2 m = 52`
      show UnpackedFloat.pack Format.binary64 (.finite _ _ _ _) = b
      unfold UnpackedFloat.pack
      simp only
      have hcat : ((1#1 : BitVec 1) ++ @unpackMantissa Format.binary64 b).toNat
          = 2 ^ 52 + (@unpackMantissa Format.binary64 b).toNat := by
        have h2 := Nat.two_pow_add_eq_or_of_lt hMlt 1
        rw [Nat.mul_one] at h2
        rw [BitVec.toNat_append]
        show 1 <<< 52 ||| _ = _
        rw [Nat.shiftLeft_eq, Nat.one_mul, ← h2]
      have hlog : ((1#1 : BitVec 1) ++ @unpackMantissa Format.binary64 b).toNat.log2 = 52 := by
        rw [hcat, Nat.log2_eq_iff (by omega)]; omega
      rw [hbias, hmb, hlog]
      split
      · omega
      · split
        · refine Eq.trans ?_ hfields
          congr 1
          · apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat]
            omega
          · apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, hcat]
            omega
        · omega

/-- `Float.Model.ofBits` is the identity on valid words. -/
theorem toBits_ofBits (x : UInt64) (h : Format.Valid Format.binary64 x.toBitVec) : (ofBits x).toBits = x := by
  show UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 x.toBitVec)) = x
  rw [pack_unpack _ h]

/-- Every model value is `ofBits` of its bits. -/
theorem ofBits_toBits (f : Float.Model) : ofBits f.toBits = f :=
  ext (toBits_ofBits _ f.valid)

end Float.Model

/-- A non-NaN word (`Srtfp.Float.isNaNPattern x = false`, spelled out) is
valid: the model's validity condition only constrains NaNs. -/
theorem Float.Model.valid_of_not_nan (x : UInt64)
    (h : (((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)) = false) :
    Float.Model.Format.binary64.Valid x.toBitVec where
  eq_packedNaN hE hM := by
    exfalso
    have hE' : x.toNat >>> 52 % 2 ^ 11 = 2047 := by
      have := congrArg BitVec.toNat hE
      simpa [Float.Model.UnpackedFloat.unpackExponent, BitVec.extractLsb, BitVec.extractLsb'_toNat] using this
    have hM' : x.toNat % 2 ^ 52 ≠ 0 := by
      intro h0; apply hM
      apply BitVec.eq_of_toNat_eq
      simpa [Float.Model.UnpackedFloat.unpackMantissa, BitVec.extractLsb, BitVec.extractLsb'_toNat] using h0
    have hE2 : (x >>> 52 &&& 0x7FF) = 0x7FF := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_and, UInt64.toNat_shiftRight,
        show (2047 : UInt64).toNat = 2 ^ 11 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
        show (52 : UInt64).toNat % 64 = 52 by decide]
      exact hE'
    have hM2 : x &&& 0xF_FFFF_FFFF_FFFF ≠ 0 := by
      intro h0; apply hM'
      have := congrArg UInt64.toNat h0
      rw [UInt64.toNat_and, show (4503599627370495 : UInt64).toNat = 2 ^ 52 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod] at this
      exact this
    have hnan : (((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)) = true := by
      rw [hE2, beq_self_eq_true, Bool.true_and, bne_iff_ne]
      exact hM2
    rw [hnan] at h
    exact Bool.noConfusion h

/-- **srtfp's runtime axiom `Float.toBits_ofBits`, as a theorem**: the statement
of `Srtfp/Float/RuntimeAxiom.lean` with `isNaNPattern` unfolded, proved over
Lean's model with no axiom. -/
theorem Float.Model.toBits_ofBits_of_not_nan (x : UInt64)
    (h : (((x >>> 52) &&& 0x7FF == 0x7FF) && (x &&& 0xF_FFFF_FFFF_FFFF != 0)) = false) :
    (Float.ofBits x).toBits = x :=
  Float.Model.toBits_ofBits x (Float.Model.valid_of_not_nan x h)
