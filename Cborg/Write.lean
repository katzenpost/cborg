-- SPDX-License-Identifier: GPL-3.0-or-later
-- Ported from Haskell cborg Codec/CBOR/Write.hs (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Encoding
import Cborg.Magic

/-!
# Cborg.Write

Serialise an `Encoding` to bytes. Every header uses the shortest form, and every
NaN is written as the canonical half-precision NaN `f9 7e 00` (RFC 8949 §4.2.2).
-/

namespace Cborg

open Magic Tokens

/-- Append a header with major type `mt` and argument `w`, in shortest form. -/
@[inline] def writeHeader (out : ByteArray) (mt : UInt8) (w : UInt64) : ByteArray :=
  let ib := mt <<< 5
  if w < 24 then out.push (ib ||| w.toUInt8)
  else if w < 0x100 then (out.push (ib ||| 24)).push w.toUInt8
  else if w < 0x10000 then pushWord16 (out.push (ib ||| 25)) w.toUInt16
  else if w < 0x100000000 then pushWord32 (out.push (ib ||| 26)) w.toUInt32
  else pushWord64 (out.push (ib ||| 27)) w

@[inline] def writeInt64 (out : ByteArray) (n : Int64) : ByteArray :=
  if n ≥ 0 then writeHeader out 0 n.toUInt64 else writeHeader out 1 (~~~ n.toUInt64)

def writeInteger (out : ByteArray) (n : Int) : ByteArray :=
  if 0 ≤ n ∧ n < 2^64 then writeHeader out 0 n.toNat.toUInt64
  else if -(2^64) ≤ n ∧ n < 0 then writeHeader out 1 (-1 - n).toNat.toUInt64
  else
    let (tag, m) := if n ≥ 0 then (0xc2, n.toNat) else (0xc3, (-1 - n).toNat)
    let bs := integerToBytes m
    writeHeader (out.push tag) 2 bs.size.toUInt64 ++ bs

@[inline] def writeCanonicalNaN (out : ByteArray) : ByteArray :=
  ((out.push 0xf9).push 0x7e).push 0x00

def writeTokens (out : ByteArray) : Tokens → ByteArray
  | TkWord w ts => writeTokens (writeHeader out 0 w) ts
  | TkInt n ts => writeTokens (writeInt64 out n) ts
  | TkBytes bs ts => writeTokens (writeHeader out 2 bs.size.toUInt64 ++ bs) ts
  | TkBytesBegin ts => writeTokens (out.push 0x5f) ts
  | TkString s ts =>
    let bs := s.toUTF8
    writeTokens (writeHeader out 3 bs.size.toUInt64 ++ bs) ts
  | TkUtf8ByteArray bs ts => writeTokens (writeHeader out 3 bs.size.toUInt64 ++ bs) ts
  | TkStringBegin ts => writeTokens (out.push 0x7f) ts
  | TkListLen n ts => writeTokens (writeHeader out 4 n) ts
  | TkListBegin ts => writeTokens (out.push 0x9f) ts
  | TkMapLen n ts => writeTokens (writeHeader out 5 n) ts
  | TkMapBegin ts => writeTokens (out.push 0xbf) ts
  | TkTag w ts => writeTokens (writeHeader out 6 w) ts
  | TkInteger n ts => writeTokens (writeInteger out n) ts
  | TkNull ts => writeTokens (out.push 0xf6) ts
  | TkUndef ts => writeTokens (out.push 0xf7) ts
  | TkBool b ts => writeTokens (out.push (if b then 0xf5 else 0xf4)) ts
  | TkSimple w ts =>
    writeTokens (if w < 24 then out.push (0xe0 ||| w) else (out.push 0xf8).push w) ts
  | TkFloat16 f ts =>
    writeTokens (if f.isNaN then writeCanonicalNaN out
                 else pushWord16 (out.push 0xf9) (floatToWord16 f)) ts
  | TkFloat32 f ts =>
    writeTokens (if f.isNaN then writeCanonicalNaN out
                 else pushWord32 (out.push 0xfa) f.toBits) ts
  | TkFloat64 f ts =>
    writeTokens (if f.isNaN then writeCanonicalNaN out
                 else pushWord64 (out.push 0xfb) f.toBits) ts
  | TkBreak ts => writeTokens (out.push 0xff) ts
  | TkEncoded bs ts => writeTokens (out ++ bs) ts
  | TkEnd => out

/-- Serialise an `Encoding` to a strict byte array. -/
def toByteArray (e : Encoding) : ByteArray :=
  writeTokens (ByteArray.emptyWithCapacity 64) e.toTokens

/-- Haskell name for `toByteArray`. -/
abbrev toStrictByteString := toByteArray

end Cborg
