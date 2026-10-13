-- SPDX-License-Identifier: GPL-3.0-or-later
-- Ported from Haskell cborg Codec/CBOR/Term.hs (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Encoding
import Cborg.Decoding

/-!
# Cborg.Term

A generic CBOR value, for when the shape of the data is not known in advance.

The indefinite-length forms keep their chunks (`TBytesI`, `TStringI`) where
Haskell uses lazy strings, so a term re-encodes to the same chunking and its
diagnostic notation shows the chunks. Equality on terms compares floats
bitwise, so a NaN equals the same NaN.
-/

namespace Cborg

inductive Term where
  | TInt (n : Int64)
  | TInteger (n : Int)
  | TBytes (bs : ByteArray)
  | TBytesI (chunks : Array ByteArray)
  | TString (s : String)
  | TStringI (chunks : Array String)
  | TList (ts : Array Term)
  | TListI (ts : Array Term)
  | TMap (kvs : Array (Term × Term))
  | TMapI (kvs : Array (Term × Term))
  | TTagged (tag : UInt64) (t : Term)
  | TBool (b : Bool)
  | TNull
  | TSimple (w : UInt8)
  | THalf (f : Float32)
  | TFloat (f : Float32)
  | TDouble (f : Float)
  deriving Inhabited

namespace Term

private def bytesEq (a b : ByteArray) : Bool := a.data == b.data

partial def beq : Term → Term → Bool
  | TInt a, TInt b => a == b
  | TInteger a, TInteger b => a == b
  | TBytes a, TBytes b => bytesEq a b
  | TBytesI a, TBytesI b => a.size == b.size && (a.zip b).all fun (x, y) => bytesEq x y
  | TString a, TString b => a == b
  | TStringI a, TStringI b => a == b
  | TList a, TList b | TListI a, TListI b =>
    a.size == b.size && (a.zip b).all fun (x, y) => beq x y
  | TMap a, TMap b | TMapI a, TMapI b =>
    a.size == b.size && (a.zip b).all fun ((k, v), (k', v')) => beq k k' && beq v v'
  | TTagged t a, TTagged t' b => t == t' && beq a b
  | TBool a, TBool b => a == b
  | TNull, TNull => true
  | TSimple a, TSimple b => a == b
  | THalf a, THalf b | TFloat a, TFloat b => a.toBits == b.toBits
  | TDouble a, TDouble b => a.toBits == b.toBits
  | _, _ => false

instance : BEq Term := ⟨beq⟩

end Term

open Term

partial def encodeTerm : Term → Encoding
  | TInt n => encodeInt n
  | TInteger n => encodeInteger n
  | TBytes bs => encodeBytes bs
  | TString s => encodeString s
  | TBytesI bss => encodeBytesIndef ++ Encoding.concat (bss.toList.map encodeBytes) ++ encodeBreak
  | TStringI sts => encodeStringIndef ++ Encoding.concat (sts.toList.map encodeString) ++ encodeBreak
  | TList ts => encodeListLen ts.size.toUInt64 ++ Encoding.concat (ts.toList.map encodeTerm)
  | TListI ts => encodeListLenIndef ++ Encoding.concat (ts.toList.map encodeTerm) ++ encodeBreak
  | TMap kvs =>
    encodeMapLen kvs.size.toUInt64 ++
      Encoding.concat (kvs.toList.map fun (k, v) => encodeTerm k ++ encodeTerm v)
  | TMapI kvs =>
    encodeMapLenIndef ++
      Encoding.concat (kvs.toList.map fun (k, v) => encodeTerm k ++ encodeTerm v) ++ encodeBreak
  | TTagged w t => encodeTag64 w ++ encodeTerm t
  | TBool b => encodeBool b
  | TNull => encodeNull
  | TSimple w => encodeSimple w
  | THalf f => encodeFloat16 f
  | TFloat f => encodeFloat f
  | TDouble f => encodeDouble f

private def maxInt : UInt64 := 0x7fffffffffffffff

mutual

/-- `decodeTerm` as a function, since `partial` needs one to recurse through. -/
partial def decodeTermU (_ : Unit) : Decoder Term := do
  let tkty ← peekTokenType
  match tkty with
  | .TypeUInt | .TypeUInt64 =>
    let w ← decodeWord
    pure (if w ≤ maxInt then TInt w.toInt64 else TInteger w.toNat)
  | .TypeNInt | .TypeNInt64 =>
    let w ← decodeNegWord
    pure (if w ≤ maxInt then TInt (-1 - w.toInt64) else TInteger (-1 - (w.toNat : Int)))
  | .TypeInteger => TInteger <$> decodeInteger
  | .TypeFloat16 => THalf <$> decodeFloat
  | .TypeFloat32 => TFloat <$> decodeFloat
  | .TypeFloat64 => TDouble <$> decodeDouble
  | .TypeBytes => TBytes <$> decodeBytes
  | .TypeBytesIndef => do decodeBytesIndef; decodeBytesIndefLen #[]
  | .TypeString => TString <$> decodeString
  | .TypeStringIndef => do decodeStringIndef; decodeStringIndefLen #[]
  | .TypeListLen | .TypeListLen64 => do
    let n ← decodeListLen
    decodeListN n (Array.mkEmpty (min n 1024))
  | .TypeListLenIndef => do decodeListLenIndef; decodeListIndefLen #[]
  | .TypeMapLen | .TypeMapLen64 => do
    let n ← decodeMapLen
    decodeMapN n (Array.mkEmpty (min n 1024))
  | .TypeMapLenIndef => do decodeMapLenIndef; decodeMapIndefLen #[]
  | .TypeTag | .TypeTag64 => do
    let x ← decodeTag64
    let y ← decodeTermU ()
    pure (TTagged x y)
  | .TypeBool => TBool <$> decodeBool
  | .TypeNull => do decodeNull; pure TNull
  | .TypeSimple => TSimple <$> decodeSimple
  | .TypeBreak => Decoder.fail "unexpected break"
  | .TypeInvalid => Decoder.fail "invalid token encoding"

partial def decodeBytesIndefLen (acc : Array ByteArray) : Decoder Term := do
  if ← decodeBreakOr then pure (TBytesI acc)
  else decodeBytesIndefLen (acc.push (← decodeBytes))

partial def decodeStringIndefLen (acc : Array String) : Decoder Term := do
  if ← decodeBreakOr then pure (TStringI acc)
  else decodeStringIndefLen (acc.push (← decodeString))

partial def decodeListN (n : Nat) (acc : Array Term) : Decoder Term :=
  match n with
  | 0 => pure (TList acc)
  | n+1 => do decodeListN n (acc.push (← decodeTermU ()))

partial def decodeListIndefLen (acc : Array Term) : Decoder Term := do
  if ← decodeBreakOr then pure (TListI acc)
  else decodeListIndefLen (acc.push (← decodeTermU ()))

partial def decodeMapN (n : Nat) (acc : Array (Term × Term)) : Decoder Term :=
  match n with
  | 0 => pure (TMap acc)
  | n+1 => do
    let k ← decodeTermU ()
    let v ← decodeTermU ()
    decodeMapN n (acc.push (k, v))

partial def decodeMapIndefLen (acc : Array (Term × Term)) : Decoder Term := do
  if ← decodeBreakOr then pure (TMapI acc)
  else
    let k ← decodeTermU ()
    let v ← decodeTermU ()
    decodeMapIndefLen (acc.push (k, v))

end

def decodeTerm : Decoder Term := decodeTermU ()

end Cborg
