-- SPDX-License-Identifier: GPL-3.0-or-later
-- Ported from Haskell cborg Codec/CBOR/Decoding.hs (BSD-3-Clause, see LICENSE.cborg).

/-!
# Cborg.Decoding

A `Decoder` is a continuation-passing monad whose steps are `DecodeAction`s:
each action names one primitive token to consume (or a peek) and carries the
continuation that receives its value. `Cborg.Read` interprets the actions
against input bytes.

Compared with Haskell: there is no `ST` state thread, so continuations are
plain functions; continuations without an argument take `Unit` so nothing runs
before the token is consumed; the 32-bit `*64` constructors and the
`ByteArray` variants are dropped; widths are carried in the Lean types
(`UInt8` … `UInt64`, `Int8` … `Int64`) and lengths are `Nat`.
-/

namespace Cborg

inductive TokenType where
  | TypeUInt
  | TypeUInt64
  | TypeNInt
  | TypeNInt64
  | TypeInteger
  | TypeFloat16
  | TypeFloat32
  | TypeFloat64
  | TypeBytes
  | TypeBytesIndef
  | TypeString
  | TypeStringIndef
  | TypeListLen
  | TypeListLen64
  | TypeListLenIndef
  | TypeMapLen
  | TypeMapLen64
  | TypeMapLenIndef
  | TypeTag
  | TypeTag64
  | TypeBool
  | TypeNull
  | TypeSimple
  | TypeBreak
  | TypeInvalid
  deriving Repr, DecidableEq, Inhabited

inductive DecodeAction (α : Type) where
  | ConsumeWord (k : UInt64 → DecodeAction α)
  | ConsumeWord8 (k : UInt8 → DecodeAction α)
  | ConsumeWord16 (k : UInt16 → DecodeAction α)
  | ConsumeWord32 (k : UInt32 → DecodeAction α)
  | ConsumeNegWord (k : UInt64 → DecodeAction α)
  | ConsumeInt (k : Int64 → DecodeAction α)
  | ConsumeInt8 (k : Int8 → DecodeAction α)
  | ConsumeInt16 (k : Int16 → DecodeAction α)
  | ConsumeInt32 (k : Int32 → DecodeAction α)
  | ConsumeListLen (k : Nat → DecodeAction α)
  | ConsumeMapLen (k : Nat → DecodeAction α)
  | ConsumeTag (k : UInt64 → DecodeAction α)

  | ConsumeInteger (k : Int → DecodeAction α)
  | ConsumeFloat (k : Float32 → DecodeAction α)
  | ConsumeDouble (k : Float → DecodeAction α)
  | ConsumeBytes (k : ByteArray → DecodeAction α)
  | ConsumeString (k : String → DecodeAction α)
  | ConsumeUtf8ByteArray (k : ByteArray → DecodeAction α)
  | ConsumeBool (k : Bool → DecodeAction α)
  | ConsumeSimple (k : UInt8 → DecodeAction α)

  | ConsumeBytesIndef (k : Unit → DecodeAction α)
  | ConsumeStringIndef (k : Unit → DecodeAction α)
  | ConsumeListLenIndef (k : Unit → DecodeAction α)
  | ConsumeMapLenIndef (k : Unit → DecodeAction α)
  | ConsumeNull (k : Unit → DecodeAction α)

  | ConsumeListLenOrIndef (k : Option Nat → DecodeAction α)
  | ConsumeMapLenOrIndef (k : Option Nat → DecodeAction α)
  | ConsumeBreakOr (k : Bool → DecodeAction α)

  | PeekTokenType (k : TokenType → DecodeAction α)
  | PeekAvailable (k : Nat → DecodeAction α)
  | PeekByteOffset (k : Nat → DecodeAction α)
  | OpenByteSpan (k : Unit → DecodeAction α)
  | CloseByteSpan (k : Unit → DecodeAction α)
  | PeekByteSpan (k : ByteArray → DecodeAction α)

  | ConsumeWordCanonical (k : UInt64 → DecodeAction α)
  | ConsumeWord8Canonical (k : UInt8 → DecodeAction α)
  | ConsumeWord16Canonical (k : UInt16 → DecodeAction α)
  | ConsumeWord32Canonical (k : UInt32 → DecodeAction α)
  | ConsumeNegWordCanonical (k : UInt64 → DecodeAction α)
  | ConsumeIntCanonical (k : Int64 → DecodeAction α)
  | ConsumeInt8Canonical (k : Int8 → DecodeAction α)
  | ConsumeInt16Canonical (k : Int16 → DecodeAction α)
  | ConsumeInt32Canonical (k : Int32 → DecodeAction α)
  | ConsumeListLenCanonical (k : Nat → DecodeAction α)
  | ConsumeMapLenCanonical (k : Nat → DecodeAction α)
  | ConsumeTagCanonical (k : UInt64 → DecodeAction α)

  | ConsumeIntegerCanonical (k : Int → DecodeAction α)
  | ConsumeFloat16Canonical (k : Float32 → DecodeAction α)
  | ConsumeFloatCanonical (k : Float32 → DecodeAction α)
  | ConsumeDoubleCanonical (k : Float → DecodeAction α)
  | ConsumeBytesCanonical (k : ByteArray → DecodeAction α)
  | ConsumeStringCanonical (k : String → DecodeAction α)
  | ConsumeUtf8ByteArrayCanonical (k : ByteArray → DecodeAction α)
  | ConsumeSimpleCanonical (k : UInt8 → DecodeAction α)

  | Fail (msg : String)
  | Done (a : α)

instance {α : Type} : Inhabited (DecodeAction α) := ⟨.Fail "inhabited"⟩

structure Decoder (α : Type) : Type 1 where
  runDecoder : {r : Type} → (α → DecodeAction r) → DecodeAction r

namespace Decoder

@[inline] protected def pure {α : Type} (a : α) : Decoder α := ⟨fun k => k a⟩

@[inline] protected def bind {α β : Type} (d : Decoder α) (f : α → Decoder β) : Decoder β :=
  ⟨fun k => d.runDecoder (fun a => (f a).runDecoder k)⟩

instance : Monad Decoder where
  pure := Decoder.pure
  bind := Decoder.bind

@[inline] def fail {α : Type} (msg : String) : Decoder α := ⟨fun _ => .Fail msg⟩

instance {α : Type} : Inhabited (Decoder α) := ⟨fail "inhabited"⟩

end Decoder

/-- Run a decoder to its first action. -/
def getDecodeAction {α : Type} (d : Decoder α) : DecodeAction α := d.runDecoder .Done

open DecodeAction

def decodeWord : Decoder UInt64 := ⟨fun k => ConsumeWord k⟩
def decodeWord8 : Decoder UInt8 := ⟨fun k => ConsumeWord8 k⟩
def decodeWord16 : Decoder UInt16 := ⟨fun k => ConsumeWord16 k⟩
def decodeWord32 : Decoder UInt32 := ⟨fun k => ConsumeWord32 k⟩
def decodeWord64 : Decoder UInt64 := ⟨fun k => ConsumeWord k⟩
/-- A negative integer token, returning `n` for the value `-1 - n`. -/
def decodeNegWord : Decoder UInt64 := ⟨fun k => ConsumeNegWord k⟩
def decodeNegWord64 : Decoder UInt64 := ⟨fun k => ConsumeNegWord k⟩
def decodeInt : Decoder Int64 := ⟨fun k => ConsumeInt k⟩
def decodeInt8 : Decoder Int8 := ⟨fun k => ConsumeInt8 k⟩
def decodeInt16 : Decoder Int16 := ⟨fun k => ConsumeInt16 k⟩
def decodeInt32 : Decoder Int32 := ⟨fun k => ConsumeInt32 k⟩
def decodeInt64 : Decoder Int64 := ⟨fun k => ConsumeInt k⟩

def decodeWordCanonical : Decoder UInt64 := ⟨fun k => ConsumeWordCanonical k⟩
def decodeWord8Canonical : Decoder UInt8 := ⟨fun k => ConsumeWord8Canonical k⟩
def decodeWord16Canonical : Decoder UInt16 := ⟨fun k => ConsumeWord16Canonical k⟩
def decodeWord32Canonical : Decoder UInt32 := ⟨fun k => ConsumeWord32Canonical k⟩
def decodeWord64Canonical : Decoder UInt64 := ⟨fun k => ConsumeWordCanonical k⟩
def decodeNegWordCanonical : Decoder UInt64 := ⟨fun k => ConsumeNegWordCanonical k⟩
def decodeNegWord64Canonical : Decoder UInt64 := ⟨fun k => ConsumeNegWordCanonical k⟩
def decodeIntCanonical : Decoder Int64 := ⟨fun k => ConsumeIntCanonical k⟩
def decodeInt8Canonical : Decoder Int8 := ⟨fun k => ConsumeInt8Canonical k⟩
def decodeInt16Canonical : Decoder Int16 := ⟨fun k => ConsumeInt16Canonical k⟩
def decodeInt32Canonical : Decoder Int32 := ⟨fun k => ConsumeInt32Canonical k⟩
def decodeInt64Canonical : Decoder Int64 := ⟨fun k => ConsumeIntCanonical k⟩

def decodeInteger : Decoder Int := ⟨fun k => ConsumeInteger k⟩
def decodeFloat : Decoder Float32 := ⟨fun k => ConsumeFloat k⟩
def decodeDouble : Decoder Float := ⟨fun k => ConsumeDouble k⟩
def decodeBytes : Decoder ByteArray := ⟨fun k => ConsumeBytes k⟩
def decodeBytesCanonical : Decoder ByteArray := ⟨fun k => ConsumeBytesCanonical k⟩
def decodeBytesIndef : Decoder Unit := ⟨fun k => ConsumeBytesIndef k⟩
/-- Haskell's unpinned-`ByteArray` decoder; the same as `decodeBytes` here. -/
def decodeByteArray : Decoder ByteArray := decodeBytes
def decodeByteArrayCanonical : Decoder ByteArray := decodeBytesCanonical
def decodeString : Decoder String := ⟨fun k => ConsumeString k⟩
def decodeStringCanonical : Decoder String := ⟨fun k => ConsumeStringCanonical k⟩
def decodeStringIndef : Decoder Unit := ⟨fun k => ConsumeStringIndef k⟩
/-- The raw bytes of a text string, without UTF-8 validation. -/
def decodeUtf8ByteArray : Decoder ByteArray := ⟨fun k => ConsumeUtf8ByteArray k⟩
def decodeUtf8ByteArrayCanonical : Decoder ByteArray :=
  ⟨fun k => ConsumeUtf8ByteArrayCanonical k⟩
def decodeListLen : Decoder Nat := ⟨fun k => ConsumeListLen k⟩
def decodeListLenCanonical : Decoder Nat := ⟨fun k => ConsumeListLenCanonical k⟩
def decodeListLenIndef : Decoder Unit := ⟨fun k => ConsumeListLenIndef k⟩
def decodeMapLen : Decoder Nat := ⟨fun k => ConsumeMapLen k⟩
def decodeMapLenCanonical : Decoder Nat := ⟨fun k => ConsumeMapLenCanonical k⟩
def decodeMapLenIndef : Decoder Unit := ⟨fun k => ConsumeMapLenIndef k⟩
def decodeTag : Decoder UInt64 := ⟨fun k => ConsumeTag k⟩
def decodeTag64 : Decoder UInt64 := ⟨fun k => ConsumeTag k⟩
def decodeTagCanonical : Decoder UInt64 := ⟨fun k => ConsumeTagCanonical k⟩
def decodeTag64Canonical : Decoder UInt64 := ⟨fun k => ConsumeTagCanonical k⟩
def decodeBool : Decoder Bool := ⟨fun k => ConsumeBool k⟩
def decodeNull : Decoder Unit := ⟨fun k => ConsumeNull k⟩
def decodeSimple : Decoder UInt8 := ⟨fun k => ConsumeSimple k⟩
def decodeIntegerCanonical : Decoder Int := ⟨fun k => ConsumeIntegerCanonical k⟩
def decodeFloat16Canonical : Decoder Float32 := ⟨fun k => ConsumeFloat16Canonical k⟩
def decodeFloatCanonical : Decoder Float32 := ⟨fun k => ConsumeFloatCanonical k⟩
def decodeDoubleCanonical : Decoder Float := ⟨fun k => ConsumeDoubleCanonical k⟩
def decodeSimpleCanonical : Decoder UInt8 := ⟨fun k => ConsumeSimpleCanonical k⟩

def decodeWordOf (n : UInt64) : Decoder Unit := do
  let n' ← decodeWord
  if n == n' then pure () else Decoder.fail s!"expected word {n}"

def decodeListLenOf (len : Nat) : Decoder Unit := do
  let len' ← decodeListLen
  if len == len' then pure () else Decoder.fail s!"expected list of length {len}"

def decodeWordCanonicalOf (n : UInt64) : Decoder Unit := do
  let n' ← decodeWordCanonical
  if n == n' then pure () else Decoder.fail s!"expected word {n}"

def decodeListLenCanonicalOf (len : Nat) : Decoder Unit := do
  let len' ← decodeListLenCanonical
  if len == len' then pure () else Decoder.fail s!"expected list of length {len}"

/-- A definite list length, or `none` for an indefinite-length list. -/
def decodeListLenOrIndef : Decoder (Option Nat) := ⟨fun k => ConsumeListLenOrIndef k⟩
def decodeMapLenOrIndef : Decoder (Option Nat) := ⟨fun k => ConsumeMapLenOrIndef k⟩
/-- Consume a break token and return `true`, or return `false` and consume nothing. -/
def decodeBreakOr : Decoder Bool := ⟨fun k => ConsumeBreakOr k⟩
def peekTokenType : Decoder TokenType := ⟨fun k => PeekTokenType k⟩
/-- Bytes available in the current input chunk. -/
def peekAvailable : Decoder Nat := ⟨fun k => PeekAvailable k⟩

abbrev ByteOffset := Nat

def peekByteOffset : Decoder ByteOffset := ⟨fun k => PeekByteOffset k⟩

def decodeWithByteOffsets {α : Type} (da : Decoder α) : Decoder (α × ByteOffset × ByteOffset) := do
  let before ← peekByteOffset
  let x ← da
  let after ← peekByteOffset
  pure (x, before, after)

abbrev ByteSpan := ByteArray

def openByteSpan : Decoder Unit := ⟨fun k => OpenByteSpan k⟩
def closeByteSpan : Decoder Unit := ⟨fun k => CloseByteSpan k⟩
def peekByteSpan : Decoder ByteSpan := ⟨fun k => PeekByteSpan k⟩

/-- Run a decoder and also return the exact input bytes it consumed. -/
def decodeWithByteSpan {α : Type} (da : Decoder α) : Decoder (α × ByteSpan) := do
  openByteSpan
  let x ← da
  let bs ← peekByteSpan
  closeByteSpan
  pure (x, bs)

/-- Decode items until a break token, folding them with `f` from `z`, then finish with `g`. -/
partial def decodeSequenceLenIndef {r a r' : Type}
    (f : r → a → r) (z : r) (g : r → r') (get : Decoder a) : Decoder r' :=
  go z
where
  go (acc : r) : Decoder r' := do
    let stop ← decodeBreakOr
    if stop then pure (g acc) else do
      let x ← get
      go (f acc x)

/-- Decode exactly `c` items, folding them with `f` from `z`, then finish with `g`. -/
def decodeSequenceLenN {r a r' : Type}
    (f : r → a → r) (z : r) (g : r → r') (c : Nat) (get : Decoder a) : Decoder r' :=
  go z c
where
  go (acc : r) : Nat → Decoder r'
    | 0 => pure (g acc)
    | n+1 => do
      let x ← get
      go (f acc x) n

end Cborg
