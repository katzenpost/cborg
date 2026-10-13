-- SPDX-License-Identifier: GPL-3.0-or-later
-- Ported from Haskell cborg Codec/CBOR/FlatTerm.hs (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Encoding
import Cborg.Decoding
import Cborg.Read

/-!
# Cborg.FlatTerm

A flat list of tokens, sitting between an `Encoding` and its bytes. It is
mostly a testing aid: an encoder can be checked against a decoder without
going through bytes, and `validFlatTerm` checks that an `Encoding` builds
well-formed CBOR.
-/

namespace Cborg

inductive TermToken where
  | TkInt (n : Int64)
  | TkInteger (n : Int)
  | TkBytes (bs : ByteArray)
  | TkBytesBegin
  | TkString (s : String)
  | TkStringBegin
  | TkListLen (n : UInt64)
  | TkListBegin
  | TkMapLen (n : UInt64)
  | TkMapBegin
  | TkBreak
  | TkTag (w : UInt64)
  | TkBool (b : Bool)
  | TkNull
  | TkSimple (w : UInt8)
  | TkFloat16 (f : Float32)
  | TkFloat32 (f : Float32)
  | TkFloat64 (f : Float)
  deriving Inhabited

abbrev FlatTerm := List TermToken

namespace TermToken

def beq : TermToken → TermToken → Bool
  | TkInt a, TkInt b => a == b
  | TkInteger a, TkInteger b => a == b
  | TkBytes a, TkBytes b => a.data == b.data
  | TkBytesBegin, TkBytesBegin => true
  | TkString a, TkString b => a == b
  | TkStringBegin, TkStringBegin => true
  | TkListLen a, TkListLen b => a == b
  | TkListBegin, TkListBegin => true
  | TkMapLen a, TkMapLen b => a == b
  | TkMapBegin, TkMapBegin => true
  | TkBreak, TkBreak => true
  | TkTag a, TkTag b => a == b
  | TkBool a, TkBool b => a == b
  | TkNull, TkNull => true
  | TkSimple a, TkSimple b => a == b
  | TkFloat16 a, TkFloat16 b | TkFloat32 a, TkFloat32 b => a.toBits == b.toBits
  | TkFloat64 a, TkFloat64 b => a.toBits == b.toBits
  | _, _ => false

instance : BEq TermToken := ⟨beq⟩

def toString : TermToken → String
  | TkInt n => s!"TkInt {n}"
  | TkInteger n => s!"TkInteger {n}"
  | TkBytes bs => s!"TkBytes {bs.toList}"
  | TkBytesBegin => "TkBytesBegin"
  | TkString s => s!"TkString {s.quote}"
  | TkStringBegin => "TkStringBegin"
  | TkListLen n => s!"TkListLen {n}"
  | TkListBegin => "TkListBegin"
  | TkMapLen n => s!"TkMapLen {n}"
  | TkMapBegin => "TkMapBegin"
  | TkBreak => "TkBreak"
  | TkTag w => s!"TkTag {w}"
  | TkBool b => s!"TkBool {b}"
  | TkNull => "TkNull"
  | TkSimple w => s!"TkSimple {w}"
  | TkFloat16 f => s!"TkFloat16 {f}"
  | TkFloat32 f => s!"TkFloat32 {f}"
  | TkFloat64 f => s!"TkFloat64 {f}"

instance : ToString TermToken := ⟨toString⟩

end TermToken

open TermToken

private def maxInt : Int := 0x7fffffffffffffff
private def minInt : Int := -0x8000000000000000

/-- An integer token, as `TkInt` when it fits an `Int64` and `TkInteger` otherwise. -/
def intToken (n : Int) : TermToken :=
  if minInt ≤ n ∧ n ≤ maxInt then TkInt n.toInt64 else TkInteger n

partial def decodeTermToken : Decoder TermToken := do
  match ← peekTokenType with
  | .TypeUInt | .TypeUInt64 => return intToken (← decodeWord).toNat
  | .TypeNInt | .TypeNInt64 => return intToken (-1 - ((← decodeNegWord).toNat : Int))
  | .TypeInteger => return TkInteger (← decodeInteger)
  | .TypeFloat16 => return TkFloat16 (← decodeFloat)
  | .TypeFloat32 => return TkFloat32 (← decodeFloat)
  | .TypeFloat64 => return TkFloat64 (← decodeDouble)
  | .TypeBytes => return TkBytes (← decodeBytes)
  | .TypeBytesIndef => do decodeBytesIndef; return TkBytesBegin
  | .TypeString => return TkString (← decodeString)
  | .TypeStringIndef => do decodeStringIndef; return TkStringBegin
  | .TypeListLen | .TypeListLen64 => return TkListLen (← decodeListLen).toUInt64
  | .TypeListLenIndef => do decodeListLenIndef; return TkListBegin
  | .TypeMapLen | .TypeMapLen64 => return TkMapLen (← decodeMapLen).toUInt64
  | .TypeMapLenIndef => do decodeMapLenIndef; return TkMapBegin
  | .TypeTag | .TypeTag64 => return TkTag (← decodeTag64)
  | .TypeBool => return TkBool (← decodeBool)
  | .TypeNull => do decodeNull; return TkNull
  | .TypeSimple => return TkSimple (← decodeSimple)
  | .TypeBreak => do let _ ← decodeBreakOr; return TkBreak
  | .TypeInvalid => Decoder.fail "invalid token encoding"

/-- Split pre-encoded CBOR into tokens. Panics on invalid CBOR, as Haskell's `error` does. -/
partial def decodePreEncoded (bs : ByteArray) : FlatTerm :=
  if bs.size == 0 then [] else
  match deserialiseFromBytes decodeTermToken bs with
  | .ok (rest, tok) => tok :: decodePreEncoded rest
  | .error e => panic! s!"toFlatTerm: encodePreEncoded used with invalid CBOR: {e}"

partial def convFlatTerm : Tokens → FlatTerm
  | .TkWord w ts => intToken w.toNat :: convFlatTerm ts
  | .TkInt n ts => TkInt n :: convFlatTerm ts
  | .TkInteger n ts => intToken n :: convFlatTerm ts
  | .TkBytes bs ts => TkBytes bs :: convFlatTerm ts
  | .TkBytesBegin ts => TkBytesBegin :: convFlatTerm ts
  | .TkString s ts => TkString s :: convFlatTerm ts
  | .TkUtf8ByteArray bs ts => TkString (String.fromUTF8! bs) :: convFlatTerm ts
  | .TkStringBegin ts => TkStringBegin :: convFlatTerm ts
  | .TkListLen n ts => TkListLen n :: convFlatTerm ts
  | .TkListBegin ts => TkListBegin :: convFlatTerm ts
  | .TkMapLen n ts => TkMapLen n :: convFlatTerm ts
  | .TkMapBegin ts => TkMapBegin :: convFlatTerm ts
  | .TkTag w ts => TkTag w :: convFlatTerm ts
  | .TkBool b ts => TkBool b :: convFlatTerm ts
  | .TkNull ts => TkNull :: convFlatTerm ts
  | .TkUndef ts => TkSimple 23 :: convFlatTerm ts
  | .TkSimple w ts => TkSimple w :: convFlatTerm ts
  | .TkFloat16 f ts => TkFloat16 f :: convFlatTerm ts
  | .TkFloat32 f ts => TkFloat32 f :: convFlatTerm ts
  | .TkFloat64 f ts => TkFloat64 f :: convFlatTerm ts
  | .TkBreak ts => TkBreak :: convFlatTerm ts
  | .TkEncoded bs ts => decodePreEncoded bs ++ convFlatTerm ts
  | .TkEnd => []

def toFlatTerm (e : Encoding) : FlatTerm := convFlatTerm e.toTokens

def tokenTypeOf : TermToken → TokenType
  | TkInt n => if n ≥ 0 then .TypeUInt else .TypeNInt
  | TkInteger n =>
    if 0 ≤ n ∧ n ≤ 0xffffffffffffffff then .TypeUInt64
    else if -0xffffffffffffffff ≤ n ∧ n < 0 then .TypeNInt64
    else .TypeInteger
  | TkBytes _ => .TypeBytes
  | TkBytesBegin => .TypeBytesIndef
  | TkString _ => .TypeString
  | TkStringBegin => .TypeStringIndef
  | TkListLen _ => .TypeListLen
  | TkListBegin => .TypeListLenIndef
  | TkMapLen _ => .TypeMapLen
  | TkMapBegin => .TypeMapLenIndef
  | TkTag _ => .TypeTag
  | TkBool _ => .TypeBool
  | TkNull => .TypeNull
  | TkBreak => .TypeBreak
  | TkSimple _ => .TypeSimple
  | TkFloat16 _ => .TypeFloat16
  | TkFloat32 _ => .TypeFloat32
  | TkFloat64 _ => .TypeFloat64

private def intOf : TermToken → Option Int
  | TkInt n => some n.toInt
  | TkInteger n => some n
  | _ => none

/-- The integer at the head of `ts`, if it lies in `[lo, hi]`. -/
private def intIn (ts : FlatTerm) (lo hi : Int) : Option (Int × FlatTerm) :=
  match ts with
  | t :: rest => match intOf t with
    | some n => if lo ≤ n ∧ n ≤ hi then some (n, rest) else none
    | none => none
  | [] => none

private def unexpected {α : Type} (name : String) : FlatTerm → Except String α
  | [] => .error s!"{name}: unexpected end of input"
  | tok :: _ => .error s!"{name}: unexpected token {tok}"

open DecodeAction in
/-- Run a decoder over a flat term. Canonical decoders behave as their plain forms. -/
partial def fromFlatTerm {α : Type} (decoder : Decoder α) (ft : FlatTerm) : Except String α :=
  go ft (getDecodeAction decoder)
where
  go (ts : FlatTerm) : DecodeAction α → Except String α
    | ConsumeWord k | ConsumeWordCanonical k =>
      match intIn ts 0 0xffffffffffffffff with
      | some (n, ts) => go ts (k n.toNat.toUInt64)
      | none => unexpected "decodeWord" ts
    | ConsumeWord8 k | ConsumeWord8Canonical k =>
      match intIn ts 0 0xff with
      | some (n, ts) => go ts (k n.toNat.toUInt8)
      | none => unexpected "decodeWord8" ts
    | ConsumeWord16 k | ConsumeWord16Canonical k =>
      match intIn ts 0 0xffff with
      | some (n, ts) => go ts (k n.toNat.toUInt16)
      | none => unexpected "decodeWord16" ts
    | ConsumeWord32 k | ConsumeWord32Canonical k =>
      match intIn ts 0 0xffffffff with
      | some (n, ts) => go ts (k n.toNat.toUInt32)
      | none => unexpected "decodeWord32" ts
    | ConsumeNegWord k | ConsumeNegWordCanonical k =>
      match intIn ts (-0x10000000000000000) (-1) with
      | some (n, ts) => go ts (k (-1 - n).toNat.toUInt64)
      | none => unexpected "decodeNegWord" ts
    | ConsumeInt k | ConsumeIntCanonical k =>
      match intIn ts minInt maxInt with
      | some (n, ts) => go ts (k n.toInt64)
      | none => unexpected "decodeInt" ts
    | ConsumeInt8 k | ConsumeInt8Canonical k =>
      match intIn ts (-0x80) 0x7f with
      | some (n, ts) => go ts (k n.toInt8)
      | none => unexpected "decodeInt8" ts
    | ConsumeInt16 k | ConsumeInt16Canonical k =>
      match intIn ts (-0x8000) 0x7fff with
      | some (n, ts) => go ts (k n.toInt16)
      | none => unexpected "decodeInt16" ts
    | ConsumeInt32 k | ConsumeInt32Canonical k =>
      match intIn ts (-0x80000000) 0x7fffffff with
      | some (n, ts) => go ts (k n.toInt32)
      | none => unexpected "decodeInt32" ts
    | ConsumeInteger k | ConsumeIntegerCanonical k =>
      match ts with
      | t :: rest => match intOf t with
        | some n => go rest (k n)
        | none => unexpected "decodeInteger" ts
      | [] => unexpected "decodeInteger" ts
    | ConsumeListLen k | ConsumeListLenCanonical k =>
      match ts with
      | TkListLen n :: rest => if n.toNat ≤ maxInt.toNat then go rest (k n.toNat)
                               else unexpected "decodeListLen" ts
      | _ => unexpected "decodeListLen" ts
    | ConsumeMapLen k | ConsumeMapLenCanonical k =>
      match ts with
      | TkMapLen n :: rest => if n.toNat ≤ maxInt.toNat then go rest (k n.toNat)
                              else unexpected "decodeMapLen" ts
      | _ => unexpected "decodeMapLen" ts
    | ConsumeTag k | ConsumeTagCanonical k =>
      match ts with
      | TkTag n :: rest => go rest (k n)
      | _ => unexpected "decodeTag" ts
    | ConsumeFloat k =>
      match ts with
      | TkFloat16 f :: rest | TkFloat32 f :: rest => go rest (k f)
      | _ => unexpected "decodeFloat" ts
    | ConsumeDouble k =>
      match ts with
      | TkFloat16 f :: rest | TkFloat32 f :: rest => go rest (k f.toFloat)
      | TkFloat64 f :: rest => go rest (k f)
      | _ => unexpected "decodeDouble" ts
    | ConsumeFloat16Canonical k =>
      match ts with
      | TkFloat16 f :: rest => go rest (k f)
      | _ => unexpected "decodeFloat16Canonical" ts
    | ConsumeFloatCanonical k =>
      match ts with
      | TkFloat32 f :: rest => go rest (k f)
      | _ => unexpected "decodeFloatCanonical" ts
    | ConsumeDoubleCanonical k =>
      match ts with
      | TkFloat64 f :: rest => go rest (k f)
      | _ => unexpected "decodeDoubleCanonical" ts
    | ConsumeBytes k | ConsumeBytesCanonical k =>
      match ts with
      | TkBytes bs :: rest => go rest (k bs)
      | _ => unexpected "decodeBytes" ts
    | ConsumeString k | ConsumeStringCanonical k =>
      match ts with
      | TkString s :: rest => go rest (k s)
      | _ => unexpected "decodeString" ts
    | ConsumeUtf8ByteArray k | ConsumeUtf8ByteArrayCanonical k =>
      match ts with
      | TkString s :: rest => go rest (k s.toUTF8)
      | _ => unexpected "decodeUtf8ByteArray" ts
    | ConsumeBool k =>
      match ts with
      | TkBool b :: rest => go rest (k b)
      | _ => unexpected "decodeBool" ts
    | ConsumeSimple k | ConsumeSimpleCanonical k =>
      match ts with
      | TkSimple w :: rest => go rest (k w)
      | _ => unexpected "decodeSimple" ts
    | ConsumeBytesIndef k =>
      match ts with
      | TkBytesBegin :: rest => go rest (k ())
      | _ => unexpected "decodeBytesIndef" ts
    | ConsumeStringIndef k =>
      match ts with
      | TkStringBegin :: rest => go rest (k ())
      | _ => unexpected "decodeStringIndef" ts
    | ConsumeListLenIndef k =>
      match ts with
      | TkListBegin :: rest => go rest (k ())
      | _ => unexpected "decodeListLenIndef" ts
    | ConsumeMapLenIndef k =>
      match ts with
      | TkMapBegin :: rest => go rest (k ())
      | _ => unexpected "decodeMapLenIndef" ts
    | ConsumeNull k =>
      match ts with
      | TkNull :: rest => go rest (k ())
      | _ => unexpected "decodeNull" ts
    | ConsumeListLenOrIndef k =>
      match ts with
      | TkListLen n :: rest => if n.toNat ≤ maxInt.toNat then go rest (k (some n.toNat))
                               else unexpected "decodeListLenOrIndef" ts
      | TkListBegin :: rest => go rest (k none)
      | _ => unexpected "decodeListLenOrIndef" ts
    | ConsumeMapLenOrIndef k =>
      match ts with
      | TkMapLen n :: rest => if n.toNat ≤ maxInt.toNat then go rest (k (some n.toNat))
                              else unexpected "decodeMapLenOrIndef" ts
      | TkMapBegin :: rest => go rest (k none)
      | _ => unexpected "decodeMapLenOrIndef" ts
    | ConsumeBreakOr k =>
      match ts with
      | TkBreak :: rest => go rest (k true)
      | _ :: _ => go ts (k false)
      | [] => unexpected "decodeBreakOr" ts
    | PeekTokenType k =>
      match ts with
      | tk :: _ => go ts (k (tokenTypeOf tk))
      | [] => unexpected "peekTokenType" ts
    | PeekAvailable k => go ts (k ts.length)
    | PeekByteOffset k => go ts (k 0)
    | OpenByteSpan k => go ts (k ())
    | CloseByteSpan k => go ts (k ())
    | PeekByteSpan k => go ts (k .empty)
    | Fail msg => .error msg
    | Done x => match ts with
      | [] => .ok x
      | _ => .error s!"trailing tokens: {ts.take 5}"

private def maxIntU : UInt64 := 0x7fffffffffffffff

mutual

private partial def validateTerm : FlatTerm → Except String FlatTerm
  | TkInt _ :: ts | TkInteger _ :: ts | TkBytes _ :: ts | TkString _ :: ts => .ok ts
  | TkBytesBegin :: ts => validateChunks (fun | TkBytes _ => true | _ => false) ts
  | TkStringBegin :: ts => validateChunks (fun | TkString _ => true | _ => false) ts
  | TkListLen len :: ts =>
    if len ≤ maxIntU then validateN len.toNat ts else .error "list len too long (> max int)"
  | TkListBegin :: ts => validateIndef 1 ts
  | TkMapLen len :: ts =>
    if len ≤ maxIntU then validateN (2 * len.toNat) ts else .error "map len too long (> max int)"
  | TkMapBegin :: ts => validateIndef 2 ts
  | TkTag _ :: ts => validateTerm ts
  | TkBool _ :: ts | TkNull :: ts | TkSimple _ :: ts => .ok ts
  | TkFloat16 _ :: ts | TkFloat32 _ :: ts | TkFloat64 _ :: ts => .ok ts
  | TkBreak :: _ => .error "unexpected token TkBreak"
  | [] => .error "unexpected end of input"

private partial def validateChunks (ok : TermToken → Bool) : FlatTerm → Except String FlatTerm
  | TkBreak :: ts => .ok ts
  | tok :: ts => if ok tok then validateChunks ok ts else .error s!"unexpected token {tok}"
  | [] => .error "unexpected end of input"

private partial def validateN : Nat → FlatTerm → Except String FlatTerm
  | 0, ts => .ok ts
  | n+1, ts => do validateN n (← validateTerm ts)

/-- Items of an indefinite list (`per` = 1) or map (`per` = 2) up to their break. -/
private partial def validateIndef (per : Nat) : FlatTerm → Except String FlatTerm
  | TkBreak :: ts => .ok ts
  | ts => do validateIndef per (← validateN per ts)

end

/-- Whether a flat term is exactly one well-formed CBOR item. -/
def validFlatTerm (ts : FlatTerm) : Bool :=
  match validateTerm ts with
  | .ok [] => true
  | _ => false

end Cborg
