-- SPDX-License-Identifier: GPL-3.0-or-later
-- Ported from Haskell cborg Codec/CBOR/Magic.hs (BSD-3-Clause, see LICENSE.cborg).

/-!
# Cborg.Magic

Low-level helpers: big-endian reads out of a `ByteArray`, big-endian writes onto
one, IEEE 754 half-precision conversion, and the big-endian byte form of
arbitrary-precision integers used by bignum tags 2 and 3.
-/

namespace Cborg.Magic

/-- Read the byte at `i`. Callers check bounds first. -/
@[inline] def eatWord8 (bs : ByteArray) (i : Nat) : UInt8 := bs[i]!

@[inline] def eatWord16 (bs : ByteArray) (i : Nat) : UInt16 :=
  (bs[i]!.toUInt16 <<< 8) ||| bs[i+1]!.toUInt16

@[inline] def eatWord32 (bs : ByteArray) (i : Nat) : UInt32 :=
  (bs[i]!.toUInt32 <<< 24) ||| (bs[i+1]!.toUInt32 <<< 16) |||
  (bs[i+2]!.toUInt32 <<< 8) ||| bs[i+3]!.toUInt32

@[inline] def eatWord64 (bs : ByteArray) (i : Nat) : UInt64 :=
  ((eatWord32 bs i).toUInt64 <<< 32) ||| (eatWord32 bs (i+4)).toUInt64

@[inline] def pushWord16 (out : ByteArray) (w : UInt16) : ByteArray :=
  (out.push (w >>> 8).toUInt8).push w.toUInt8

@[inline] def pushWord32 (out : ByteArray) (w : UInt32) : ByteArray :=
  pushWord16 (pushWord16 out (w >>> 16).toUInt16) w.toUInt16

@[inline] def pushWord64 (out : ByteArray) (w : UInt64) : ByteArray :=
  pushWord32 (pushWord32 out (w >>> 32).toUInt32) w.toUInt32

/-- Widen a half-precision bit pattern to single precision. Exact. -/
def wordToFloat16 (h : UInt16) : Float32 :=
  let sign : UInt32 := (h.toUInt32 &&& 0x8000) <<< 16
  let e := (h >>> 10) &&& 0x1f
  let m := (h &&& 0x3ff).toUInt32
  if e == 0x1f then
    Float32.ofBits (sign ||| (0x7f800000 : UInt32) ||| (m <<< 13))
  else if e != 0 then
    Float32.ofBits (sign ||| ((e.toUInt32 + 112) <<< 23) ||| (m <<< 13))
  else if m == 0 then
    Float32.ofBits sign
  else
    -- subnormal half: normalise the mantissa
    let rec norm (m : UInt32) (e : UInt32) : Nat → UInt32 × UInt32
      | 0 => (m, e)
      | n+1 => if m &&& 0x400 != 0 then (m, e) else norm (m <<< 1) (e - 1) n
    let (m', e') := norm m 113 11
    Float32.ofBits (sign ||| (e' <<< 23) ||| ((m' &&& 0x3ff) <<< 13))

/-- Narrow single precision to half precision, rounding to nearest even. -/
def floatToWord16 (f : Float32) : UInt16 :=
  let bits := f.toBits
  let sign : UInt16 := ((bits >>> 16) &&& 0x8000).toUInt16
  let exp := (bits >>> 23) &&& 0xff
  let mant := bits &&& 0x7fffff
  if exp == 0xff then
    if mant == 0 then sign ||| (0x7c00 : UInt16)
    else sign ||| (0x7e00 : UInt16) ||| (mant >>> 13).toUInt16
  else
    let e : Int := (exp.toNat : Int) - 127 + 15
    if e ≥ 31 then sign ||| (0x7c00 : UInt16)
    else if e ≤ 0 then
      if e < -10 then sign
      else
        let m := mant ||| 0x800000
        let shift := (14 - e).toNat.toUInt32
        let half := m >>> shift
        let rem := m &&& ((1 <<< shift) - 1)
        let halfway := (1 : UInt32) <<< (shift - 1)
        let half := if rem > halfway || (rem == halfway && half &&& 1 == 1) then half + 1 else half
        sign ||| half.toUInt16
    else
      let half : UInt16 := sign ||| (e.toNat.toUInt16 <<< 10) ||| (mant >>> 13).toUInt16
      let rem := mant &&& 0x1fff
      if rem > 0x1000 || (rem == 0x1000 && half &&& 1 == 1) then half + 1 else half

@[inline] def wordToFloat32 (w : UInt32) : Float32 := Float32.ofBits w
@[inline] def wordToFloat64 (w : UInt64) : Float := Float.ofBits w

/-- Big-endian bytes of a non-negative integer; `0` is the single byte `0x00`. -/
def integerToBytes (n : Nat) : ByteArray :=
  if n == 0 then ⟨#[0]⟩
  else
    let rec go (n : Nat) (acc : List UInt8) : List UInt8 :=
      if h : n = 0 then acc else go (n / 256) ((n % 256).toUInt8 :: acc)
    termination_by n
    decreasing_by omega
    ⟨(go n []).toArray⟩

/-- The non-negative integer denoted by big-endian bytes. -/
def uintegerFromBytes (bs : ByteArray) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

def nintegerFromBytes (bs : ByteArray) : Int :=
  -1 - (uintegerFromBytes bs : Int)

end Cborg.Magic
