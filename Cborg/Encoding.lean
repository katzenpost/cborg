-- SPDX-License-Identifier: GPL-3.0-or-later
-- Ported from Haskell cborg Codec/CBOR/Encoding.hs (BSD-3-Clause, see LICENSE.cborg).

/-!
# Cborg.Encoding

An `Encoding` is a difference list of `Tokens`: each `encode*` function prepends
one token, and `++` composes encodings in constant time. `Cborg.Write` turns the
token stream into bytes.

Haskell's machine-word pairs (`TkWord`/`TkWord64`, `TkInt`/`TkInt64`,
`TkTag`/`TkTag64`) collapse into one 64-bit constructor each, and the
`ByteArray`-backed tokens are gone because Lean's `ByteArray` already is one.
-/

namespace Cborg

inductive Tokens where
  -- Positive and negative integers (type 0,1)
  | TkWord (w : UInt64) (ts : Tokens)
  | TkInt (n : Int64) (ts : Tokens)
  -- Bytes and string (type 2,3)
  | TkBytes (bs : ByteArray) (ts : Tokens)
  | TkBytesBegin (ts : Tokens)
  | TkString (s : String) (ts : Tokens)
  | TkUtf8ByteArray (bs : ByteArray) (ts : Tokens)
  | TkStringBegin (ts : Tokens)
  -- Structures (type 4,5)
  | TkListLen (n : UInt64) (ts : Tokens)
  | TkListBegin (ts : Tokens)
  | TkMapLen (n : UInt64) (ts : Tokens)
  | TkMapBegin (ts : Tokens)
  -- Tagged values (type 6)
  | TkTag (w : UInt64) (ts : Tokens)
  | TkInteger (n : Int) (ts : Tokens)
  -- Simple and floats (type 7)
  | TkNull (ts : Tokens)
  | TkUndef (ts : Tokens)
  | TkBool (b : Bool) (ts : Tokens)
  | TkSimple (w : UInt8) (ts : Tokens)
  | TkFloat16 (f : Float32) (ts : Tokens)
  | TkFloat32 (f : Float32) (ts : Tokens)
  | TkFloat64 (f : Float) (ts : Tokens)
  | TkBreak (ts : Tokens)
  -- Special
  | TkEncoded (bs : ByteArray) (ts : Tokens)
  | TkEnd
  deriving Inhabited

structure Encoding where
  run : Tokens → Tokens

namespace Encoding

instance : Append Encoding := ⟨fun a b => ⟨fun ts => a.run (b.run ts)⟩⟩
instance : EmptyCollection Encoding := ⟨⟨id⟩⟩
instance : Inhabited Encoding := ⟨⟨id⟩⟩

def empty : Encoding := ⟨id⟩

/-- `mconcat`: concatenate encodings left to right. -/
def concat (es : List Encoding) : Encoding := es.foldr (· ++ ·) empty

def toTokens (e : Encoding) : Tokens := e.run .TkEnd

end Encoding

open Tokens

def encodeWord (w : UInt64) : Encoding := ⟨TkWord w⟩
def encodeWord8 (w : UInt8) : Encoding := ⟨TkWord w.toUInt64⟩
def encodeWord16 (w : UInt16) : Encoding := ⟨TkWord w.toUInt64⟩
def encodeWord32 (w : UInt32) : Encoding := ⟨TkWord w.toUInt64⟩
def encodeWord64 (w : UInt64) : Encoding := ⟨TkWord w⟩
def encodeInt (n : Int64) : Encoding := ⟨TkInt n⟩
def encodeInt8 (n : Int8) : Encoding := ⟨TkInt n.toInt64⟩
def encodeInt16 (n : Int16) : Encoding := ⟨TkInt n.toInt64⟩
def encodeInt32 (n : Int32) : Encoding := ⟨TkInt n.toInt64⟩
def encodeInt64 (n : Int64) : Encoding := ⟨TkInt n⟩
def encodeInteger (n : Int) : Encoding := ⟨TkInteger n⟩
def encodeBytes (bs : ByteArray) : Encoding := ⟨TkBytes bs⟩
def encodeBytesIndef : Encoding := ⟨TkBytesBegin⟩
def encodeString (s : String) : Encoding := ⟨TkString s⟩
def encodeStringIndef : Encoding := ⟨TkStringBegin⟩
/-- Encode bytes that the caller guarantees are valid UTF-8 as a text string. -/
def encodeUtf8ByteArray (bs : ByteArray) : Encoding := ⟨TkUtf8ByteArray bs⟩
def encodeListLen (n : UInt64) : Encoding := ⟨TkListLen n⟩
def encodeListLenIndef : Encoding := ⟨TkListBegin⟩
def encodeMapLen (n : UInt64) : Encoding := ⟨TkMapLen n⟩
def encodeMapLenIndef : Encoding := ⟨TkMapBegin⟩
def encodeBreak : Encoding := ⟨TkBreak⟩
def encodeTag (w : UInt64) : Encoding := ⟨TkTag w⟩
def encodeTag64 (w : UInt64) : Encoding := ⟨TkTag w⟩
def encodeBool (b : Bool) : Encoding := ⟨TkBool b⟩
def encodeUndef : Encoding := ⟨TkUndef⟩
def encodeNull : Encoding := ⟨TkNull⟩
def encodeSimple (w : UInt8) : Encoding := ⟨TkSimple w⟩
def encodeFloat16 (f : Float32) : Encoding := ⟨TkFloat16 f⟩
def encodeFloat (f : Float32) : Encoding := ⟨TkFloat32 f⟩
def encodeDouble (f : Float) : Encoding := ⟨TkFloat64 f⟩
/-- Splice in bytes that are already a valid CBOR encoding. Not checked. -/
def encodePreEncoded (bs : ByteArray) : Encoding := ⟨TkEncoded bs⟩

end Cborg
