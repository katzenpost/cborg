-- SPDX-License-Identifier: GPL-3.0-or-later
-- Ported from Haskell cborg Codec/CBOR/Read.hs (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Decoding
import Cborg.Magic

/-!
# Cborg.Read

Run a `Decoder` against input bytes. One interpreter, `step`, executes
`DecodeAction`s over a buffer until the decoder finishes, fails, or needs a
token that runs past the end of the buffer. `deserialiseFromBytes` treats the
last case as "end of input"; `deserialiseIncremental` asks for another chunk
and resumes at the same action, since every token is consumed atomically.

Haskell splits this into a fast path over one chunk and a slow path across
chunks; with Lean's strict `ByteArray` one path suffices.
-/

namespace Cborg

open Magic DecodeAction TokenType

structure DeserialiseFailure where
  offset : ByteOffset
  msg : String
  deriving Repr, BEq, Inhabited

instance : ToString DeserialiseFailure where
  toString e := s!"Cborg: deserialising failed at offset {e.offset} : {e.msg}"

namespace Read

/-- Result of reading one token at a position. -/
inductive Tok (α : Type) where
  | short
  | bad
  | ok (a : α) (sz : Nat)

/-- The largest `Int` in Haskell, which bounds lengths and `decodeInt`. -/
def maxInt : UInt64 := 0x7fffffffffffffff

/-- Read a header whose initial byte satisfies `accept`, returning its argument. -/
@[inline] def header (bs : ByteArray) (pos : Nat) (accept : UInt8 → Bool) : Tok UInt64 :=
  if pos ≥ bs.size then .short else
  let ib := bs[pos]!
  if !accept ib then .bad else
  let ai := ib &&& 31
  if ai < 24 then .ok ai.toUInt64 1
  else if ai == 24 then
    if pos + 2 ≤ bs.size then .ok (eatWord8 bs (pos+1)).toUInt64 2 else .short
  else if ai == 25 then
    if pos + 3 ≤ bs.size then .ok (eatWord16 bs (pos+1)).toUInt64 3 else .short
  else if ai == 26 then
    if pos + 5 ≤ bs.size then .ok (eatWord32 bs (pos+1)).toUInt64 5 else .short
  else if ai == 27 then
    if pos + 9 ≤ bs.size then .ok (eatWord64 bs (pos+1)) 9 else .short
  else .bad

@[inline] def major (mt : UInt8) (ib : UInt8) : Bool := ib >>> 5 == mt

/-- A header argument is canonical when no shorter header could hold it. -/
@[inline] def isWordCanonical (sz : Nat) (w : UInt64) : Bool :=
  if sz == 2 then w > 0x17
  else if sz == 3 then w > 0xff
  else if sz == 5 then w > 0xffff
  else if sz == 9 then w > 0xffffffff
  else true

/-- A signed integer token (major type 0 or 1) that fits in an `Int64`. -/
@[inline] def intTok (bs : ByteArray) (pos : Nat) : Tok Int64 :=
  match header bs pos (fun ib => ib >>> 5 ≤ 1) with
  | .short => .short
  | .bad => .bad
  | .ok w sz =>
    if w > maxInt then .bad
    else if bs[pos]! >>> 5 == 0 then .ok w.toInt64 sz
    else .ok (-1 - w.toInt64) sz

/-- A definite-length byte or text string of major type `mt`: (canonical?, bytes). -/
@[inline] def stringTok (bs : ByteArray) (pos : Nat) (mt : UInt8) : Tok (Bool × ByteArray) :=
  match header bs pos (major mt) with
  | .short => .short
  | .bad => .bad
  | .ok len sz =>
    if len > maxInt then .bad
    else
      let start := pos + sz
      let stop := start + len.toNat
      if stop > bs.size then .short
      else .ok (isWordCanonical sz len, bs.extract start stop) (sz + len.toNat)

def isBigIntRepCanonical (bstr : ByteArray) : Bool :=
  bstr.size > 8 && bstr[0]! != 0

/-- An integer: major type 0 or 1, or a bignum (tag 2 or 3 then bytes): (canonical?, value). -/
def integerTok (bs : ByteArray) (pos : Nat) : Tok (Bool × Int) :=
  if pos ≥ bs.size then .short else
  let ib := bs[pos]!
  if ib == 0xc2 || ib == 0xc3 then
    match stringTok bs (pos + 1) 2 with
    | .short => .short
    | .bad => .bad
    | .ok (canon, bstr) sz =>
      let canon := canon && isBigIntRepCanonical bstr
      let n : Int := if ib == 0xc2 then uintegerFromBytes bstr else nintegerFromBytes bstr
      .ok (canon, n) (sz + 1)
  else
    match header bs pos (fun ib => ib >>> 5 ≤ 1) with
    | .short => .short
    | .bad => .bad
    | .ok w sz =>
      let n : Int := if ib >>> 5 == 0 then w.toNat else -1 - (w.toNat : Int)
      .ok (isWordCanonical sz w, n) sz

/-- A half, single or double float, as its width in bytes plus its value as a double. -/
@[inline] def floatTok (bs : ByteArray) (pos : Nat) (allowDouble : Bool) : Tok (Float32 ⊕ Float) :=
  if pos ≥ bs.size then .short else
  match bs[pos]! with
  | 0xf9 => if pos + 3 ≤ bs.size then .ok (.inl (wordToFloat16 (eatWord16 bs (pos+1)))) 3 else .short
  | 0xfa => if pos + 5 ≤ bs.size then .ok (.inl (wordToFloat32 (eatWord32 bs (pos+1)))) 5 else .short
  | 0xfb =>
    if !allowDouble then .bad
    else if pos + 9 ≤ bs.size then .ok (.inr (wordToFloat64 (eatWord64 bs (pos+1)))) 9 else .short
  | _ => .bad

@[inline] def toDouble : Float32 ⊕ Float → Float
  | .inl f => f.toFloat
  | .inr d => d

@[inline] def toSingle : Float32 ⊕ Float → Float32
  | .inl f => f
  | .inr d => d.toFloat32

/-- RFC 7049 §3.9: the only canonical NaN is the half-precision `f9 7e 00`. -/
@[inline] def isCanonicalNaN (bs : ByteArray) (pos sz : Nat) : Bool :=
  sz == 3 && eatWord16 bs (pos+1) == 0x7e00

@[inline] def simpleTok (bs : ByteArray) (pos : Nat) : Tok UInt8 :=
  if pos ≥ bs.size then .short else
  let ib := bs[pos]!
  if 0xe0 ≤ ib && ib ≤ 0xf7 then .ok (ib - 0xe0) 1
  else if ib == 0xf8 then
    if pos + 2 ≤ bs.size then .ok bs[pos+1]! 2 else .short
  else .bad

def tokenTypeOf (ib : UInt8) : TokenType :=
  let ai := ib &&& 31
  if 28 ≤ ai && ai ≤ 30 then TypeInvalid else
  match ib >>> 5 with
  | 0 => if ai < 27 then TypeUInt else if ai == 27 then TypeUInt64 else TypeInvalid
  | 1 => if ai < 27 then TypeNInt else if ai == 27 then TypeNInt64 else TypeInvalid
  | 2 => if ai == 31 then TypeBytesIndef else TypeBytes
  | 3 => if ai == 31 then TypeStringIndef else TypeString
  | 4 => if ai < 27 then TypeListLen else if ai == 27 then TypeListLen64 else TypeListLenIndef
  | 5 => if ai < 27 then TypeMapLen else if ai == 27 then TypeMapLen64 else TypeMapLenIndef
  | 6 =>
    if ai == 2 || ai == 3 then TypeInteger
    else if ai < 27 then TypeTag else if ai == 27 then TypeTag64 else TypeInvalid
  | _ =>
    if ai < 20 then TypeSimple
    else if ai == 20 || ai == 21 then TypeBool
    else if ai == 22 then TypeNull
    else if ai == 23 || ai == 24 then TypeSimple
    else if ai == 25 then TypeFloat16
    else if ai == 26 then TypeFloat32
    else if ai == 27 then TypeFloat64
    else TypeBreak

inductive Step (α : Type) where
  | done (pos : Nat) (a : α)
  | fail (pos : Nat) (msg : String)
  /-- The action at `pos` needs bytes past the end of the buffer. -/
  | needMore (pos : Nat) (marks : List Nat) (da : DecodeAction α)

instance {α : Type} : Inhabited (Step α) := ⟨.fail 0 "inhabited"⟩

/-- Bytes the decoder has consumed since the innermost open byte span. -/
def spanFrom (bs : ByteArray) (base pos : Nat) : List Nat → ByteArray
  | [] => .empty
  | m :: _ => bs.extract (m - base) pos

/--
Execute actions over `bs`, whose first byte sits at absolute offset `base`.
`marks` holds the absolute offsets of open byte spans, innermost first.
-/
partial def step {α : Type} (bs : ByteArray) (base : Nat) (marks : List Nat) (pos : Nat) :
    DecodeAction α → Step α
  | .Done a => .done pos a
  | .Fail msg => .fail pos msg
  | da@(ConsumeWord k) =>
    match header bs pos (major 0) with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected word"
    | .ok w sz => step bs base marks (pos + sz) (k w)
  | da@(ConsumeWord8 k) =>
    match header bs pos (major 0) with
    | .short => .needMore pos marks da
    | .ok w sz => if w ≤ 0xff then step bs base marks (pos + sz) (k w.toUInt8)
                  else .fail pos "expected word8"
    | .bad => .fail pos "expected word8"
  | da@(ConsumeWord16 k) =>
    match header bs pos (major 0) with
    | .short => .needMore pos marks da
    | .ok w sz => if w ≤ 0xffff then step bs base marks (pos + sz) (k w.toUInt16)
                  else .fail pos "expected word16"
    | .bad => .fail pos "expected word16"
  | da@(ConsumeWord32 k) =>
    match header bs pos (major 0) with
    | .short => .needMore pos marks da
    | .ok w sz => if w ≤ 0xffffffff then step bs base marks (pos + sz) (k w.toUInt32)
                  else .fail pos "expected word32"
    | .bad => .fail pos "expected word32"
  | da@(ConsumeNegWord k) =>
    match header bs pos (major 1) with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected negative int"
    | .ok w sz => step bs base marks (pos + sz) (k w)
  | da@(ConsumeInt k) =>
    match intTok bs pos with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected int"
    | .ok n sz => step bs base marks (pos + sz) (k n)
  | da@(ConsumeInt8 k) =>
    match intTok bs pos with
    | .short => .needMore pos marks da
    | .ok n sz => if -0x80 ≤ n && n ≤ 0x7f then step bs base marks (pos + sz) (k n.toInt8)
                  else .fail pos "expected int8"
    | .bad => .fail pos "expected int8"
  | da@(ConsumeInt16 k) =>
    match intTok bs pos with
    | .short => .needMore pos marks da
    | .ok n sz => if -0x8000 ≤ n && n ≤ 0x7fff then step bs base marks (pos + sz) (k n.toInt16)
                  else .fail pos "expected int16"
    | .bad => .fail pos "expected int16"
  | da@(ConsumeInt32 k) =>
    match intTok bs pos with
    | .short => .needMore pos marks da
    | .ok n sz =>
      if -0x80000000 ≤ n && n ≤ 0x7fffffff then step bs base marks (pos + sz) (k n.toInt32)
      else .fail pos "expected int32"
    | .bad => .fail pos "expected int32"
  | da@(ConsumeListLen k) =>
    match header bs pos (major 4) with
    | .short => .needMore pos marks da
    | .ok n sz => if n ≤ maxInt then step bs base marks (pos + sz) (k n.toNat)
                  else .fail pos "expected list len"
    | .bad => .fail pos "expected list len"
  | da@(ConsumeMapLen k) =>
    match header bs pos (major 5) with
    | .short => .needMore pos marks da
    | .ok n sz => if n ≤ maxInt then step bs base marks (pos + sz) (k n.toNat)
                  else .fail pos "expected map len"
    | .bad => .fail pos "expected map len"
  | da@(ConsumeTag k) =>
    match header bs pos (major 6) with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected tag"
    | .ok w sz => step bs base marks (pos + sz) (k w)

  | da@(ConsumeInteger k) =>
    match integerTok bs pos with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected integer"
    | .ok (_, n) sz => step bs base marks (pos + sz) (k n)
  | da@(ConsumeFloat k) =>
    match floatTok bs pos false with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected float"
    | .ok f sz => step bs base marks (pos + sz) (k (toSingle f))
  | da@(ConsumeDouble k) =>
    match floatTok bs pos true with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected double"
    | .ok f sz => step bs base marks (pos + sz) (k (toDouble f))
  | da@(ConsumeBytes k) =>
    match stringTok bs pos 2 with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected bytes"
    | .ok (_, b) sz => step bs base marks (pos + sz) (k b)
  | da@(ConsumeString k) =>
    match stringTok bs pos 3 with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected string"
    | .ok (_, b) sz =>
      match String.fromUTF8? b with
      | some s => step bs base marks (pos + sz) (k s)
      | none => .fail pos "invalid UTF8"
  | da@(ConsumeUtf8ByteArray k) =>
    match stringTok bs pos 3 with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected string"
    | .ok (_, b) sz => step bs base marks (pos + sz) (k b)
  | da@(ConsumeBool k) =>
    if pos ≥ bs.size then .needMore pos marks da
    else match bs[pos]! with
      | 0xf4 => step bs base marks (pos + 1) (k false)
      | 0xf5 => step bs base marks (pos + 1) (k true)
      | _ => .fail pos "expected bool"
  | da@(ConsumeSimple k) =>
    match simpleTok bs pos with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected simple"
    | .ok w sz => step bs base marks (pos + sz) (k w)

  | da@(ConsumeBytesIndef k) =>
    if pos ≥ bs.size then .needMore pos marks da
    else if bs[pos]! == 0x5f then step bs base marks (pos + 1) (k ())
    else .fail pos "expected bytes start"
  | da@(ConsumeStringIndef k) =>
    if pos ≥ bs.size then .needMore pos marks da
    else if bs[pos]! == 0x7f then step bs base marks (pos + 1) (k ())
    else .fail pos "expected string start"
  | da@(ConsumeListLenIndef k) =>
    if pos ≥ bs.size then .needMore pos marks da
    else if bs[pos]! == 0x9f then step bs base marks (pos + 1) (k ())
    else .fail pos "expected list start"
  | da@(ConsumeMapLenIndef k) =>
    if pos ≥ bs.size then .needMore pos marks da
    else if bs[pos]! == 0xbf then step bs base marks (pos + 1) (k ())
    else .fail pos "expected map start"
  | da@(ConsumeNull k) =>
    if pos ≥ bs.size then .needMore pos marks da
    else if bs[pos]! == 0xf6 then step bs base marks (pos + 1) (k ())
    else .fail pos "expected null"

  | da@(ConsumeListLenOrIndef k) =>
    if pos < bs.size && bs[pos]! == 0x9f then step bs base marks (pos + 1) (k none)
    else match header bs pos (major 4) with
      | .short => .needMore pos marks da
      | .ok n sz => if n ≤ maxInt then step bs base marks (pos + sz) (k (some n.toNat))
                    else .fail pos "expected list len or indef"
      | .bad => .fail pos "expected list len or indef"
  | da@(ConsumeMapLenOrIndef k) =>
    if pos < bs.size && bs[pos]! == 0xbf then step bs base marks (pos + 1) (k none)
    else match header bs pos (major 5) with
      | .short => .needMore pos marks da
      | .ok n sz => if n ≤ maxInt then step bs base marks (pos + sz) (k (some n.toNat))
                    else .fail pos "expected map len or indef"
      | .bad => .fail pos "expected map len or indef"
  | da@(ConsumeBreakOr k) =>
    if pos ≥ bs.size then .needMore pos marks da
    else if bs[pos]! == 0xff then step bs base marks (pos + 1) (k true)
    else step bs base marks pos (k false)

  | da@(PeekTokenType k) =>
    if pos ≥ bs.size then .needMore pos marks da
    else step bs base marks pos (k (tokenTypeOf bs[pos]!))
  | PeekAvailable k => step bs base marks pos (k (bs.size - pos))
  | PeekByteOffset k => step bs base marks pos (k (base + pos))
  | OpenByteSpan k => step bs base ((base + pos) :: marks) pos (k ())
  | CloseByteSpan k => step bs base marks.tail pos (k ())
  | PeekByteSpan k => step bs base marks pos (k (spanFrom bs base pos marks))

  | da@(ConsumeWordCanonical k) =>
    match header bs pos (major 0) with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected word"
    | .ok w sz => if isWordCanonical sz w then step bs base marks (pos + sz) (k w)
                  else .fail pos "non-canonical word"
  | da@(ConsumeWord8Canonical k) =>
    match header bs pos (major 0) with
    | .short => .needMore pos marks da
    | .ok w sz =>
      if w > 0xff then .fail pos "expected word8"
      else if isWordCanonical sz w then step bs base marks (pos + sz) (k w.toUInt8)
      else .fail pos "non-canonical word8"
    | .bad => .fail pos "expected word8"
  | da@(ConsumeWord16Canonical k) =>
    match header bs pos (major 0) with
    | .short => .needMore pos marks da
    | .ok w sz =>
      if w > 0xffff then .fail pos "expected word16"
      else if isWordCanonical sz w then step bs base marks (pos + sz) (k w.toUInt16)
      else .fail pos "non-canonical word16"
    | .bad => .fail pos "expected word16"
  | da@(ConsumeWord32Canonical k) =>
    match header bs pos (major 0) with
    | .short => .needMore pos marks da
    | .ok w sz =>
      if w > 0xffffffff then .fail pos "expected word32"
      else if isWordCanonical sz w then step bs base marks (pos + sz) (k w.toUInt32)
      else .fail pos "non-canonical word32"
    | .bad => .fail pos "expected word32"
  | da@(ConsumeNegWordCanonical k) =>
    match header bs pos (major 1) with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected negative int"
    | .ok w sz => if isWordCanonical sz w then step bs base marks (pos + sz) (k w)
                  else .fail pos "non-canonical negative int"
  | da@(ConsumeIntCanonical k) =>
    match intTok bs pos, header bs pos (fun ib => ib >>> 5 ≤ 1) with
    | .short, _ => .needMore pos marks da
    | .ok n sz, .ok w _ => if isWordCanonical sz w then step bs base marks (pos + sz) (k n)
                           else .fail pos "non-canonical int"
    | _, _ => .fail pos "expected int"
  | da@(ConsumeInt8Canonical k) =>
    match intTok bs pos, header bs pos (fun ib => ib >>> 5 ≤ 1) with
    | .short, _ => .needMore pos marks da
    | .ok n sz, .ok w _ =>
      if !(-0x80 ≤ n && n ≤ 0x7f) then .fail pos "expected int8"
      else if isWordCanonical sz w then step bs base marks (pos + sz) (k n.toInt8)
      else .fail pos "non-canonical int8"
    | _, _ => .fail pos "expected int8"
  | da@(ConsumeInt16Canonical k) =>
    match intTok bs pos, header bs pos (fun ib => ib >>> 5 ≤ 1) with
    | .short, _ => .needMore pos marks da
    | .ok n sz, .ok w _ =>
      if !(-0x8000 ≤ n && n ≤ 0x7fff) then .fail pos "expected int16"
      else if isWordCanonical sz w then step bs base marks (pos + sz) (k n.toInt16)
      else .fail pos "non-canonical int16"
    | _, _ => .fail pos "expected int16"
  | da@(ConsumeInt32Canonical k) =>
    match intTok bs pos, header bs pos (fun ib => ib >>> 5 ≤ 1) with
    | .short, _ => .needMore pos marks da
    | .ok n sz, .ok w _ =>
      if !(-0x80000000 ≤ n && n ≤ 0x7fffffff) then .fail pos "expected int32"
      else if isWordCanonical sz w then step bs base marks (pos + sz) (k n.toInt32)
      else .fail pos "non-canonical int32"
    | _, _ => .fail pos "expected int32"
  | da@(ConsumeListLenCanonical k) =>
    match header bs pos (major 4) with
    | .short => .needMore pos marks da
    | .ok n sz =>
      if n > maxInt then .fail pos "expected list len"
      else if isWordCanonical sz n then step bs base marks (pos + sz) (k n.toNat)
      else .fail pos "non-canonical list len"
    | .bad => .fail pos "expected list len"
  | da@(ConsumeMapLenCanonical k) =>
    match header bs pos (major 5) with
    | .short => .needMore pos marks da
    | .ok n sz =>
      if n > maxInt then .fail pos "expected map len"
      else if isWordCanonical sz n then step bs base marks (pos + sz) (k n.toNat)
      else .fail pos "non-canonical map len"
    | .bad => .fail pos "expected map len"
  | da@(ConsumeTagCanonical k) =>
    match header bs pos (major 6) with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected tag"
    | .ok w sz => if isWordCanonical sz w then step bs base marks (pos + sz) (k w)
                  else .fail pos "non-canonical tag"

  | da@(ConsumeIntegerCanonical k) =>
    match integerTok bs pos with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected integer"
    | .ok (canon, n) sz => if canon then step bs base marks (pos + sz) (k n)
                           else .fail pos "non-canonical integer"
  | da@(ConsumeFloat16Canonical k) =>
    match floatTok bs pos false with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected float"
    | .ok f sz =>
      let f := toSingle f
      let canon := sz == 3 && (!f.isNaN || isCanonicalNaN bs pos sz)
      if canon then step bs base marks (pos + sz) (k f) else .fail pos "non-canonical float16"
  | da@(ConsumeFloatCanonical k) =>
    match floatTok bs pos false with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected float"
    | .ok f sz =>
      let f := toSingle f
      let canon := if f.isNaN then isCanonicalNaN bs pos sz else sz == 5
      if canon then step bs base marks (pos + sz) (k f) else .fail pos "non-canonical float"
  | da@(ConsumeDoubleCanonical k) =>
    match floatTok bs pos true with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected double"
    | .ok f sz =>
      let f := toDouble f
      let canon := if f.isNaN then isCanonicalNaN bs pos sz else sz == 9
      if canon then step bs base marks (pos + sz) (k f) else .fail pos "non-canonical double"
  | da@(ConsumeBytesCanonical k) =>
    match stringTok bs pos 2 with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected bytes"
    | .ok (canon, b) sz => if canon then step bs base marks (pos + sz) (k b)
                           else .fail pos "non-canonical length prefix"
  | da@(ConsumeStringCanonical k) =>
    match stringTok bs pos 3 with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected string"
    | .ok (canon, b) sz =>
      if !canon then .fail pos "non-canonical length prefix"
      else match String.fromUTF8? b with
        | some s => step bs base marks (pos + sz) (k s)
        | none => .fail pos "invalid UTF8"
  | da@(ConsumeUtf8ByteArrayCanonical k) =>
    match stringTok bs pos 3 with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected string"
    | .ok (canon, b) sz => if canon then step bs base marks (pos + sz) (k b)
                           else .fail pos "non-canonical length prefix"
  | da@(ConsumeSimpleCanonical k) =>
    match simpleTok bs pos with
    | .short => .needMore pos marks da
    | .bad => .fail pos "expected simple"
    | .ok w sz => if sz != 2 || w > 0x17 then step bs base marks (pos + sz) (k w)
                  else .fail pos "non-canonical simple"

end Read

open Read

/-- Decode one value from the start of `bs`, returning it with the unconsumed bytes and the offset reached. -/
def deserialiseFromBytesWithSize {α : Type} (d : Decoder α) (bs : ByteArray) :
    Except DeserialiseFailure (ByteArray × ByteOffset × α) :=
  match step bs 0 [] 0 (getDecodeAction d) with
  | .done pos a => .ok (bs.extract pos bs.size, pos, a)
  | .fail pos msg => .error ⟨pos, msg⟩
  | .needMore pos _ _ => .error ⟨pos, "end of input"⟩

/-- Decode one value from the start of `bs`, returning it with the unconsumed bytes. -/
def deserialiseFromBytes {α : Type} (d : Decoder α) (bs : ByteArray) :
    Except DeserialiseFailure (ByteArray × α) :=
  (deserialiseFromBytesWithSize d bs).map fun (rest, _, a) => (rest, a)

/-- An incremental decode in progress. -/
inductive IDecode (α : Type) where
  /-- More input is needed: pass the next chunk, or `none` at end of input. -/
  | Partial (k : Option ByteArray → IDecode α)
  | Done (rest : ByteArray) (offset : ByteOffset) (a : α)
  | Fail (rest : ByteArray) (offset : ByteOffset) (err : DeserialiseFailure)

instance {α : Type} : Inhabited (IDecode α) := ⟨.Fail .empty 0 default⟩

namespace Read

/--
How many bytes from `pos` the token there needs, judged from what is
available: its header, plus the body of a definite-length string or bignum.
-/
def tokenNeed (bs : ByteArray) (pos : Nat) : Nat :=
  if pos ≥ bs.size then 1 else
  let ib := bs[pos]!
  let ai := ib &&& 31
  let hs := if ai < 24 then 1 else if ai == 24 then 2 else if ai == 25 then 3
    else if ai == 26 then 5 else if ai == 27 then 9 else 1
  if ib == 0xc2 || ib == 0xc3 then 1 + tokenNeed bs (pos + 1)
  else if (ib >>> 5 == 2 || ib >>> 5 == 3) && ai < 28 then
    match header bs pos (fun _ => true) with
    | .ok len sz => sz + len.toNat
    | _ => hs
  else hs
termination_by bs.size - pos
decreasing_by
  all_goals simp_wf
  all_goals omega

def concatChunks (buf : ByteArray) (pos : Nat) (chunks : Array ByteArray) (total : Nat) : ByteArray :=
  chunks.foldl (· ++ ·) ((ByteArray.emptyWithCapacity (buf.size - pos + total)).append
    (buf.extract pos buf.size))

/-- The input has ended: a decoder that asks for more has run out. -/
def atEnd {α : Type} : IDecode α → IDecode α
  | .Partial k => k none
  | r => r

mutual

/--
Resume over `buf`, whose first byte is at absolute offset `base`. On running
short, keep only the bytes from the earliest of `pos` and any open byte span,
then wait for enough chunks to complete the stalled token.
-/
partial def resume {α : Type} (buf : ByteArray) (base : Nat) (marks : List Nat) (pos : Nat)
    (da : DecodeAction α) : IDecode α :=
  match step buf base marks pos da with
  | .done pos a => .Done (buf.extract pos buf.size) (base + pos) a
  | .fail pos msg => .Fail (buf.extract pos buf.size) (base + pos) ⟨base + pos, msg⟩
  | .needMore pos marks da =>
    let keep := marks.foldl (fun m o => min m (o - base)) pos
    waitFor buf base marks keep (pos - keep) da (tokenNeed buf pos) #[] 0

/--
Collect chunks until the buffer from `keep` holds `need` bytes past `pos`, then
join them once. Copying the buffer on every chunk instead would make decoding a
long string arrive in many chunks quadratic.
-/
partial def waitFor {α : Type} (buf : ByteArray) (base : Nat) (marks : List Nat) (keep pos : Nat)
    (da : DecodeAction α) (need : Nat) (chunks : Array ByteArray) (total : Nat) : IDecode α :=
  .Partial fun
    | none =>
      if chunks.isEmpty then
        .Fail (buf.extract (keep + pos) buf.size) (base + keep + pos) ⟨base + keep + pos, "end of input"⟩
      else
        atEnd (resume (concatChunks buf keep chunks total) (base + keep) marks pos da)
    | some chunk =>
      let chunks := chunks.push chunk
      let total := total + chunk.size
      if buf.size - keep - pos + total ≥ need then
        resume (concatChunks buf keep chunks total) (base + keep) marks pos da
      else waitFor buf base marks keep pos da need chunks total

end

end Read

/-- Start decoding incrementally; feed input through `IDecode.Partial`. -/
def deserialiseIncremental {α : Type} (d : Decoder α) : IDecode α :=
  match getDecodeAction d with
  | .Done a => .Done .empty 0 a
  | .Fail msg => .Fail .empty 0 ⟨0, msg⟩
  | da => .Partial fun
    | none => Read.atEnd (Read.resume .empty 0 [] 0 da)
    | some chunk => Read.resume chunk 0 [] 0 da

end Cborg
