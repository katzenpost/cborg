-- SPDX-License-Identifier: GPL-3.0-or-later
-- Follows Haskell serialise Codec/Serialise/Class.hs (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Write
import Cborg.Read
import Cborg.Term
import Std.Data.HashSet

/-!
# Cborg.Serialise

The `Serialise` class pairs an encoder with a decoder for a type, as in
Haskell's `serialise` package, with instances for the basic types.

`Option α` differs from Haskell: `none` is CBOR `null`, the way Go, Rust and
Python CBOR libraries write optional fields, rather than a zero- or
one-element list.

The record helpers, which `serialise` does not have, cover structs sent as
maps keyed by field name: a missing key and a `null` value both read as an
absent optional field, and unknown keys can be ignored or rejected.
-/

namespace Cborg

class Serialise (α : Type) where
  encode : α → Encoding
  decode : Decoder α

export Serialise (encode decode)

def serialise {α : Type} [Serialise α] (a : α) : ByteArray := toByteArray (encode a)

/-- Decode exactly one value, failing on trailing bytes. -/
def deserialise {α : Type} [Serialise α] (bs : ByteArray) : Except DeserialiseFailure α :=
  match deserialiseFromBytesWithSize decode bs with
  | .ok (rest, off, a) => if rest.size == 0 then .ok a else .error ⟨off, "trailing bytes"⟩
  | .error e => .error e

/-- Lift a failure-or-value into a decoder. -/
def Decoder.ofExcept {α : Type} : Except String α → Decoder α
  | .ok a => pure a
  | .error msg => Decoder.fail msg

instance : Serialise Unit := ⟨fun _ => encodeNull, decodeNull⟩
instance : Serialise Bool := ⟨encodeBool, decodeBool⟩
instance : Serialise UInt8 := ⟨encodeWord8, decodeWord8⟩
instance : Serialise UInt16 := ⟨encodeWord16, decodeWord16⟩
instance : Serialise UInt32 := ⟨encodeWord32, decodeWord32⟩
instance : Serialise UInt64 := ⟨encodeWord64, decodeWord64⟩
instance : Serialise Int8 := ⟨encodeInt8, decodeInt8⟩
instance : Serialise Int16 := ⟨encodeInt16, decodeInt16⟩
instance : Serialise Int32 := ⟨encodeInt32, decodeInt32⟩
instance : Serialise Int64 := ⟨encodeInt64, decodeInt64⟩
instance : Serialise Int := ⟨encodeInteger, decodeInteger⟩
instance : Serialise Float32 := ⟨encodeFloat, decodeFloat⟩
instance : Serialise Float := ⟨encodeDouble, decodeDouble⟩
instance : Serialise String := ⟨encodeString, decodeString⟩
instance : Serialise ByteArray := ⟨encodeBytes, decodeBytes⟩
instance : Serialise Term := ⟨encodeTerm, decodeTerm⟩

instance : Serialise Nat where
  encode n := encodeInteger n
  decode := do
    let n ← decodeInteger
    if n < 0 then Decoder.fail "expected natural number" else pure n.toNat

/-- `none` is `null`; anything else is the value itself. -/
instance {α : Type} [Serialise α] : Serialise (Option α) where
  encode
    | none => encodeNull
    | some a => encode a
  decode := do
    if (← peekTokenType) == .TypeNull then decodeNull; pure none
    else some <$> decode

/-- Decode the items of a definite or indefinite-length list. -/
def decodeListOf {α : Type} (d : Decoder α) : Decoder (Array α) := do
  match ← decodeListLenOrIndef with
  | some n => decodeSequenceLenN Array.push (Array.mkEmpty (min n 1024)) id n d
  | none => decodeSequenceLenIndef Array.push #[] id d

instance {α : Type} [Serialise α] : Serialise (Array α) where
  encode as := encodeListLen as.size.toUInt64 ++ as.foldl (fun e a => e ++ encode a) Encoding.empty
  decode := decodeListOf decode

instance {α : Type} [Serialise α] : Serialise (List α) where
  encode as := encode as.toArray
  decode := Array.toList <$> decodeListOf decode

/-- Pairs are two-element lists. -/
instance {α β : Type} [Serialise α] [Serialise β] : Serialise (α × β) where
  encode | (a, b) => encodeListLen 2 ++ encode a ++ encode b
  decode := do
    decodeListLenOf 2
    let a ← decode
    let b ← decode
    pure (a, b)

/-- A byte string of exactly `n` bytes, such as a 16-byte message ID. -/
structure FixedBytes (n : Nat) where
  bytes : ByteArray
  size_eq : bytes.size = n

instance {n : Nat} : Serialise (FixedBytes n) where
  encode b := encodeBytes b.bytes
  decode := do
    let bs ← decodeBytes
    if h : bs.size = n then pure ⟨bs, h⟩
    else Decoder.fail s!"expected {n} bytes, got {bs.size}"

/-! ## Records: maps keyed by field name -/

/-- A map with text keys whose values are kept as their encoded bytes until asked for. -/
structure Record where
  fields : Array (String × ByteArray)

/-- Decode a map with text keys, definite or indefinite. Duplicate keys fail. -/
def decodeRecord : Decoder Record := do
  let entry : Decoder (String × ByteArray) := do
    let k ← decodeString
    let (_, raw) ← decodeWithByteSpan decodeTerm
    pure (k, raw)
  let fields ← match ← decodeMapLenOrIndef with
    | some n => decodeSequenceLenN Array.push (Array.mkEmpty (min n 1024)) id n entry
    | none => decodeSequenceLenIndef Array.push #[] id entry
  let mut seen : Std.HashSet String := {}
  for (k, _) in fields do
    if seen.contains k then Decoder.fail s!"duplicate key {k.quote}"
    seen := seen.insert k
  pure ⟨fields⟩

namespace Record

def raw? (r : Record) (key : String) : Option ByteArray :=
  r.fields.find? (·.1 == key) |>.map (·.2)

/-- An optional field: `none` if the key is missing or its value is `null`. -/
def optional {α : Type} [Serialise α] (r : Record) (key : String) : Decoder (Option α) :=
  match r.raw? key with
  | none => pure none
  | some raw =>
    match deserialise (α := Option α) raw with
    | .ok a => pure a
    | .error e => Decoder.fail s!"field {key.quote}: {e.msg}"

/-- A required field. -/
def required {α : Type} [Serialise α] (r : Record) (key : String) : Decoder α := do
  match ← r.optional (α := α) key with
  | some a => pure a
  | none => Decoder.fail s!"missing field {key.quote}"

/-- A field that falls back to a default when missing or `null`. -/
def withDefault {α : Type} [Serialise α] (r : Record) (key : String) (dflt : α) : Decoder α := do
  return (← r.optional key).getD dflt

/-- Fail if the record has a key not in `keys`. -/
def onlyKeys (r : Record) (keys : List String) : Decoder Unit := do
  for (k, _) in r.fields do
    if !keys.contains k then Decoder.fail s!"unknown field {k.quote}"

end Record

/-- A record re-encodes its fields' bytes as they were. -/
instance : Serialise Record where
  encode r := encodeMapLen r.fields.size.toUInt64 ++
    r.fields.foldl (fun acc (k, v) => acc ++ encodeString k ++ encodePreEncoded v) Encoding.empty
  decode := decodeRecord

/-- One field of a record to encode; `none` leaves the key out. -/
abbrev Field := String × Option Encoding

def field {α : Type} [Serialise α] (key : String) (a : α) : Field := (key, some (encode a))

/-- An optional field written only when present. -/
def optField {α : Type} [Serialise α] (key : String) : Option α → Field
  | none => (key, none)
  | some a => (key, some (encode a))

/-- An optional field written as `null` when absent. -/
def nullableField {α : Type} [Serialise α] (key : String) (a : Option α) : Field :=
  (key, some (encode a))

/-- A definite-length map of the present fields, in the order given. -/
def encodeRecord (fields : List Field) : Encoding :=
  let present := fields.filterMap fun (k, e) => e.map (k, ·)
  encodeMapLen present.length.toUInt64 ++
    present.foldl (fun acc (k, e) => acc ++ encodeString k ++ e) Encoding.empty

end Cborg
