/- All-UInt64 192-bit `shiftedSig` kernel using the wider pow10 table.

The 128-bit `shiftedSig_u64_kernel` (in `Uint64Kernel.lean`) requires the
auxiliary value `B = 2^qNeg · 10^kPos < 2^64` for soundness; when `B` is
large (as for subnormals like `5e-324`, very-small floats like `1e-10`,
and very-large floats like `1.8e308`), the orchestration falls through
to the slow-path `shiftedSig m q k` (boxed-Nat spec), which dominates
the per-call cost for those inputs.

The 192-bit table (`pow10Table192`) carries 64 more bits of precision,
which is enough for the multiply-shift to compute the floor correctly
*without* the B guard.  Trade-off: one extra 64×64 mul (the `gMid`
limb) per call.

This file defines the 192-bit kernel and a `_v4` orchestration that uses
it.  Proof bridges + csimp wiring live in `Uint64Bridge192.lean`
(future commit).
-/
import Srtfp.Schubfach
import Srtfp.Schubfach.Perf.Orchestration
import Srtfp.Schubfach.Perf.Pow10Table192
import Srtfp.Schubfach.Perf.Uint64Kernel
import Srtfp.Schubfach.MulHigh128

namespace Srtfp.Schubfach


/-! ## Pure-UInt64 192-bit `shiftedSig` kernel

Computes `s = ⌊m · 10^k · 2^q⌋` for binary64 inputs via:
  - 192-bit pow10 lookup `g ≈ 10^{-k} · 2^h` (h = h192)
  - 64×192-bit multiply: `P = m · g`, a 256-bit value
  - Right shift by `shiftAmt = h - q`

For binary64 inputs, `shiftAmt ∈ [188, 256)` (about 64 higher than the
128-bit kernel's `[124, 192)` range due to the precision shift).
At the highest shiftAmt values, `P >> shiftAmt` lives entirely in the
top 64 bits, so the result is just an arithmetic right shift on `rHi`. -/

/-- The 192-bit multiply-shift kernel.  Computes `(mU · g192) >> shiftAmtU`
    where `g192 = gHi·2^128 + gMid·2^64 + gLo`.  The product is up to
    `60 + 192 = 252` bits (since `mU < 2^60`), kept as a 256-bit quadruple
    `(qHi, qMidHi, qMidLo, qLo)` of UInt64s.

    Caller preconditions for the result to match `shiftedSig`:
    - `mU < 2^60` (binary64 mantissa bound)
    - `gHi, gMid, gLo = pow10Lookup192 (-k)` for `k ∈ [-308, 308]`
    - `shiftAmtU = UInt64.ofNat shiftAmt.toNat` with
      `shiftAmt = h192 - q ∈ [188, 256)`. -/
@[inline]
def shiftedSig_u192_kernel
    (mU : UInt64) (gHi gMid gLo : UInt64) (shiftAmtU : UInt64) : UInt64 :=
  -- Compute the 256-bit product P = mU · g192.
  -- P = mU · gLo + (mU · gMid) << 64 + (mU · gHi) << 128
  -- Each `mU · limb` is a 128-bit product giving (limbHi, limbLo).
  let pLoLo  : UInt64 := mU * gLo
  let pLoHi  : UInt64 := mulHi64 mU gLo
  let pMidLo : UInt64 := mU * gMid
  let pMidHi : UInt64 := mulHi64 mU gMid
  let pHiLo  : UInt64 := mU * gHi
  let pHiHi  : UInt64 := mulHi64 mU gHi
  -- Aggregate into 4 limbs (qHi, qMidHi, qMidLo, qLo):
  --   qLo    = pLoLo                                    [bits 0..63]
  --   qMidLo = pLoHi + pMidLo                           [bits 64..127]  + carry from below
  --   qMidHi = pMidHi + pHiLo + carry                   [bits 128..191] + carry
  --   qHi    = pHiHi + carry                            [bits 192..255]
  let qLo : UInt64 := pLoLo
  -- Layer 1: pLoHi + pMidLo, may carry.
  let s1 : UInt64 := pLoHi + pMidLo
  let c1 : UInt64 := if s1 < pLoHi then 1 else 0
  let qMidLo : UInt64 := s1
  -- Layer 2: pMidHi + pHiLo + c1.  Two adds; second may carry on either.
  let s2a : UInt64 := pMidHi + pHiLo
  let c2a : UInt64 := if s2a < pMidHi then 1 else 0
  let s2b : UInt64 := s2a + c1
  let c2b : UInt64 := if s2b < s2a then 1 else 0
  let qMidHi : UInt64 := s2b
  let carryToHi : UInt64 := c2a + c2b
  -- Layer 3: pHiHi + carryToHi.  pHiHi < 2^60 - tiny, carryToHi ≤ 2, no overflow.
  let qHi : UInt64 := pHiHi + carryToHi
  -- Now right-shift P by shiftAmtU.
  -- For binary64 inputs, shiftAmtU is in [188, 256).  We handle 4 cases:
  --   < 64:   result spans qLo..qMidLo
  --   < 128:  result spans qMidLo..qMidHi
  --   < 192:  result spans qMidHi..qHi
  --   ≥ 192:  result is in qHi only
  if shiftAmtU < 64 then
    if shiftAmtU = 0 then qLo
    else (qLo >>> shiftAmtU) ||| (qMidLo <<< (64 - shiftAmtU))
  else if shiftAmtU < 128 then
    let s64 := shiftAmtU - 64
    if s64 = 0 then qMidLo
    else (qMidLo >>> s64) ||| (qMidHi <<< (64 - s64))
  else if shiftAmtU < 192 then
    let s64 := shiftAmtU - 128
    if s64 = 0 then qMidHi
    else (qMidHi >>> s64) ||| (qHi <<< (64 - s64))
  else
    let s64 := shiftAmtU - 192
    qHi >>> s64

/-! ## `shiftedSig_v4` orchestration

Drop-in replacement for `shiftedSig_v3` that uses the 192-bit kernel.
No B-guard needed: precision is sufficient on the wider table.

Falls back to the spec for inputs outside the table range. -/

/-- 192-bit `shiftedSig` fast path.  Computes `shiftedSig m q k` via the
    192-bit multiply-shift kernel, without the cheap-B / spec fallback.

    Width guards (structural; never fire on real binary64):
    - `m < 2^60`
    - `k ∈ [-pow10Table192_kMax, pow10Table192_kMax]` (so `-k ∈ [-kMax, kMax]`)
    - `shiftAmt = h192 - q ∈ [188, 256)` (the table-derived shift range)

    The final guard is the binary64-domain check
    `0<m<2^53 ∧ -1074≤q≤971 ∧ k = kOfMQ m q`.  On it, R20
    (`residueR20Cond_decode_binary64`) makes the 192-bit kernel correct
    over the *entire* binary64 range — no `B < 2^k` accuracy guard.  This
    mirrors `shiftedSig_v3`'s widened 128-bit path.  Off the domain, fall
    through to `shiftedSig m q k` (spec); for real binary64 inputs the
    kernel branch is always taken. -/
@[inline]
def shiftedSig_v4 (m : Nat) (q : Int) (k : Int) : Nat :=
  let sigTuple := pow10Lookup192 (-k)
  let sigGHi := sigTuple.1
  let sigGMid := sigTuple.2.1
  let sigGLo := sigTuple.2.2.1
  let sigH := sigTuple.2.2.2
  let sigShiftAmt : Int := sigH - q
  if _h_m : m ≥ (1 <<< 60 : Nat) then shiftedSig m q k
  else if _h_k_lo : (-k : Int) < pow10Table192_kMin then shiftedSig m q k
  else if _h_k_hi : (-k : Int) > pow10Table192_kMax then shiftedSig m q k
  else if _h_s_lo : sigShiftAmt < 188 then shiftedSig m q k
  else if _h_s_hi : sigShiftAmt ≥ 256 then shiftedSig m q k
  else if _h_dom : 0 < m ∧ m < 2 ^ 53 ∧ -1074 ≤ q ∧ q ≤ 971 ∧ k = kOfMQ m q then
    let mU : UInt64 := UInt64.ofNat m
    let shiftAmtU : UInt64 := UInt64.ofNat sigShiftAmt.toNat
    (shiftedSig_u192_kernel mU sigGHi sigGMid sigGLo shiftAmtU).toNat
  else
    shiftedSig m q k

/-! ## Runtime cross-check helper (no proof)

For test/bench purposes, expose a function comparing `shiftedSig_v4 = shiftedSig_v3`
on a list of `(m, q, k)` triples. -/

end Srtfp.Schubfach
