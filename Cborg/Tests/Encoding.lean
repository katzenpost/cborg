-- SPDX-License-Identifier: GPL-3.0-or-later
-- Unit tests, including ports of Haskell cborg tests/Tests/Regress/*.hs
-- (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Tests.Util

/-!
# Unit tests

Exact encoder output at every header-width boundary, float narrowing and NaN
canonicalisation, decoder failures with their messages and offsets, and the
regression cases from Haskell cborg.
-/

namespace Cborg.Tests.Encoding

open Term

def enc (name : String) (e : Encoding) (expected : String) : TestM Unit :=
  checkEq s!"encode {name}" expected (hex (toByteArray e))

def failsWith {α : Type} (name : String) (d : Decoder α) (input : String)
    (offset : Nat) (msg : String) : TestM Unit :=
  match deserialiseFromBytes d (unhex input) with
  | .ok _ => check name false fun _ => "decoded, expected failure"
  | .error e => checkEq name s!"{offset}: {msg}" s!"{e.offset}: {e.msg}"

def decodes {α : Type} [BEq α] [ToString α] (name : String) (d : Decoder α) (input : String)
    (expected : α) : TestM Unit :=
  match decodeAll d (unhex input) with
  | .ok a => checkEq name expected a
  | .error e => check name false fun _ => e

def headers : TestM Unit := do
  enc "0" (encodeWord 0) "00"
  enc "23" (encodeWord 23) "17"
  enc "24" (encodeWord 24) "1818"
  enc "255" (encodeWord 255) "18ff"
  enc "256" (encodeWord 256) "190100"
  enc "65535" (encodeWord 65535) "19ffff"
  enc "65536" (encodeWord 65536) "1a00010000"
  enc "2^32-1" (encodeWord 0xffffffff) "1affffffff"
  enc "2^32" (encodeWord 0x100000000) "1b0000000100000000"
  enc "2^64-1" (encodeWord 0xffffffffffffffff) "1bffffffffffffffff"
  enc "-1" (encodeInt (-1)) "20"
  enc "-24" (encodeInt (-24)) "37"
  enc "-25" (encodeInt (-25)) "3818"
  enc "-256" (encodeInt (-256)) "38ff"
  enc "-257" (encodeInt (-257)) "390100"
  enc "Int64 min" (encodeInt64 (-9223372036854775808)) "3b7fffffffffffffff"
  enc "Int64 max" (encodeInt64 9223372036854775807) "1b7fffffffffffffff"
  enc "Int8" (encodeInt8 (-128)) "387f"
  enc "Word8" (encodeWord8 200) "18c8"
  enc "Integer 2^64" (encodeInteger (2^64)) "c249010000000000000000"
  enc "Integer -2^64" (encodeInteger (-(2^64))) "3bffffffffffffffff"
  enc "Integer -2^64-1" (encodeInteger (-(2^64) - 1)) "c349010000000000000000"
  enc "Integer small" (encodeInteger 500) "1901f4"
  enc "list 24" (encodeListLen 24) "9818"
  enc "map 1000" (encodeMapLen 1000) "b903e8"
  enc "tag 0" (encodeTag 0) "c0"
  enc "tag 2^32" (encodeTag64 0x100000000) "db0000000100000000"
  enc "bytes 24" (encodeBytes (ByteArray.mk (Array.replicate 24 0xaa)))
    ("5818" ++ String.join (List.replicate 24 "aa"))
  enc "string" (encodeString "IETF") "6449455446"
  enc "utf8 string" (encodeString "水") "63e6b0b4"
  enc "utf8 bytearray" (encodeUtf8ByteArray "ü".toUTF8) "62c3bc"
  enc "indef" (encodeListLenIndef ++ encodeBytesIndef ++ encodeStringIndef ++ encodeMapLenIndef
    ++ encodeBreak) "9f5f7fbfff"
  enc "simple" (encodeBool false ++ encodeBool true ++ encodeNull ++ encodeUndef ++ encodeSimple 16
    ++ encodeSimple 255) "f4f5f6f7f0f8ff"
  enc "pre-encoded" (encodeListLen 2 ++ encodePreEncoded (unhex "6161") ++ encodeWord 1) "82616101"

def floats : TestM Unit := do
  enc "half 1.0" (encodeFloat16 1.0) "f93c00"
  enc "half 65504" (encodeFloat16 65504.0) "f97bff"
  enc "half overflow" (encodeFloat16 65520.0) "f97c00"
  enc "half smallest subnormal" (encodeFloat16 (5.960464477539063e-8 : Float).toFloat32) "f90001"
  enc "half underflow" (encodeFloat16 (2.9e-8 : Float).toFloat32) "f90000"
  enc "half round to even" (encodeFloat16 (1.0 + 2.0 ^ (-11.0) : Float).toFloat32) "f93c00"
  enc "half round up" (encodeFloat16 (1.0 + 3.0 * 2.0 ^ (-11.0) : Float).toFloat32) "f93c02"
  enc "half -0" (encodeFloat16 (-0.0)) "f98000"
  enc "half -inf" (encodeFloat16 (-1.0 / 0.0)) "f9fc00"
  enc "float 100000" (encodeFloat 100000.0) "fa47c35000"
  enc "double 1.1" (encodeDouble 1.1) "fb3ff199999999999a"
  enc "half NaN" (encodeFloat16 (0.0 / 0.0)) "f97e00"
  enc "float NaN" (encodeFloat (0.0 / 0.0)) "f97e00"
  enc "double NaN" (encodeDouble (Float.ofBits 0x7ff0000000000001)) "f97e00"
  -- every half-precision bit pattern survives widening and narrowing
  let mut bad := 0
  for i in [0:0x10000] do
    let h := i.toUInt16
    let isNaN := (h &&& 0x7c00) == 0x7c00 && (h &&& 0x3ff) != 0
    if !isNaN && Magic.floatToWord16 (Magic.wordToFloat16 h) != h then bad := bad + 1
  checkEq "half widen/narrow round trip" 0 bad

def failures : TestM Unit := do
  failsWith "word from string" decodeWord "6161" 0 "expected word"
  failsWith "word8 too big" decodeWord8 "190100" 0 "expected word8"
  failsWith "int8 too small" decodeInt8 "3880" 0 "expected int8"
  failsWith "int beyond Int64" decodeInt "1b8000000000000000" 0 "expected int"
  failsWith "truncated header" decodeWord "19ff" 0 "end of input"
  failsWith "empty input" decodeWord "" 0 "end of input"
  failsWith "truncated bytes" decodeBytes "4401" 0 "end of input"
  failsWith "bool from null" decodeBool "f6" 0 "expected bool"
  failsWith "reserved additional info" decodeTerm "1c" 0 "invalid token encoding"
  failsWith "stray break" decodeTerm "ff" 0 "unexpected break"
  failsWith "second item fails at its offset" (do let _ ← decodeWord; decodeWord) "0161" 1
    "expected word"
  failsWith "non-canonical word" decodeWordCanonical "1817" 0 "non-canonical word"
  failsWith "non-canonical length" decodeBytesCanonical "580101" 0 "non-canonical length prefix"
  failsWith "non-canonical float" decodeFloatCanonical "f93c00" 0 "non-canonical float"
  failsWith "non-canonical NaN" decodeDoubleCanonical "fb7ff8000000000000" 0 "non-canonical double"
  failsWith "non-canonical simple" decodeSimpleCanonical "f810" 0 "non-canonical simple"
  failsWith "list len of" (decodeListLenOf 2) "83" 1 "expected list of length 2"
  decodes "NaN is canonical as f97e00" (Float.isNaN <$> decodeDoubleCanonical) "f97e00" true
  decodes "word canonical 24" decodeWordCanonical "1818" 24
  decodes "simple 255" decodeSimpleCanonical "f8ff" 255
  decodes "simple 16" decodeSimple "f0" 16
  decodes "double from half" decodeDouble "f93e00" 1.5
  decodes "float from half" decodeFloat "f9c400" (-4.0)
  decodes "integer from bignum" decodeInteger "c249010000000000000000" (2^64)
  decodes "integer from nint" decodeInteger "3bffffffffffffffff" (-(2^64))
  decodes "list len or indef" decodeListLenOrIndef "9f" none
  decodes "map len or indef" decodeMapLenOrIndef "a3" (some 3)
  decodes "break or" (do let b ← decodeBreakOr; let w ← decodeWord; pure (b, w)) "05" (false, 5)
  decodes "utf8 byte array" decodeUtf8ByteArray "62c3bc" "ü".toUTF8
  decodes "peek token type" (toString <$> (do let t ← peekTokenType; let _ ← decodeTerm; pure (repr t)))
    "c249010000000000000000" "Cborg.TokenType.TypeInteger"

/-- Haskell cborg issue 160: malformed lengths and strings fail cleanly. -/
def issue160 : TestM Unit := do
  failsWith "non-utf8 string" decodeString "6180" 0 "invalid UTF8"
  failsWith "list length beyond Int" decodeListLen "9bffffffffffffffff" 0 "expected list len"
  failsWith "map length beyond Int" decodeMapLen "bbffffffffffffffff" 0 "expected map len"
  failsWith "bytes length beyond Int" decodeBytes
    ("5bffffffffffffffff" ++ String.join (List.replicate 100 "00")) 0 "expected bytes"
  failsWith "huge bytes length" decodeBytes "5b7fffffffffffffff00" 0 "end of input"

/--
Haskell cborg issue 162: a non-canonical bignum fails canonical decoding, also
deep inside a larger item. Haskell reports offset 34 for the composite case,
the end of the bad token; this port reports 29, where the token starts.
-/
def issue162 : TestM Unit := do
  let bigBytesDecoder : Decoder Unit := do
    let _ ← decodeListLenCanonical; let _ ← decodeMapLenCanonical
    let _ ← decodeListLenCanonical; let _ ← decodeListLenCanonical
    let _ ← decodeWord16Canonical; let _ ← decodeWord16Canonical; let _ ← decodeWord8Canonical
    let _ ← decodeMapLenCanonical; let _ ← decodeMapLenCanonical; let _ ← decodeMapLenCanonical
    let _ ← decodeListLenCanonical; let _ ← decodeWord8Canonical
    let _ ← decodeListLenCanonical; let _ ← decodeListLenCanonical
    let _ ← decodeMapLenCanonical; let _ ← decodeWord8Canonical
    let _ ← decodeListLenCanonical; let _ ← decodeIntegerCanonical
    let _ ← decodeWord32Canonical; let _ ← decodeWord8Canonical
    let _ ← decodeListLenCanonical; let _ ← decodeIntegerCanonical
    let _ ← decodeWord32Canonical
  let nonCanonicalInteger := "c2430908a1"
  failsWith "issue 162 simple" decodeIntegerCanonical nonCanonicalInteger 0 "non-canonical integer"
  failsWith "issue 162 composite" bigBytesDecoder
    ("87a08183000000a0a0a081008081a200821a0004ecf91a1aeb977a0182" ++ nonCanonicalInteger
      ++ "1a05ee4d20") 29 "non-canonical integer"

/-- Haskell cborg's FlatTerm regressions. -/
def flatTermRegress : TestM Unit := do
  let largeWord : UInt64 := 0x8000000000000000
  check "flat term large word" (fromFlatTerm decodeWord (toFlatTerm (encodeWord largeWord)) == .ok largeWord)
  let smallInt : Int64 := -9223372036854775808
  check "flat term Int64 min" (fromFlatTerm decodeInt64 (toFlatTerm (encodeInt64 smallInt)) == .ok smallInt)
  check "flat term undef" (toFlatTerm encodeUndef == [.TkSimple 23])
  check "flat term pre-encoded" (toFlatTerm (encodePreEncoded (unhex "820102")) ==
    [.TkListLen 2, .TkInt 1, .TkInt 2])
  check "valid flat term" (validFlatTerm (toFlatTerm (encodeListLen 2 ++ encodeWord 1 ++ encodeNull)))
  check "invalid flat term: short list" (!validFlatTerm (toFlatTerm (encodeListLen 2 ++ encodeWord 1)))
  check "invalid flat term: stray break" (!validFlatTerm (toFlatTerm encodeBreak))
  check "invalid flat term: trailing" (!validFlatTerm (toFlatTerm (encodeWord 1 ++ encodeWord 2)))

def main : IO UInt32 :=
  runSuite "Encoding" do
    headers
    floats
    failures
    issue160
    issue162
    flatTermRegress

end Cborg.Tests.Encoding

def main : IO UInt32 := Cborg.Tests.Encoding.main
