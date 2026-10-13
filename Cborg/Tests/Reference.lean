-- SPDX-License-Identifier: GPL-3.0-or-later
-- Ported from Haskell cborg tests/Tests/Reference.hs and Tests/Reference/TestVectors.hs
-- (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Tests.Util
import Lean.Data.Json

/-!
# RFC 7049 Appendix A

Each example is decoded with `decodeTerm`, compared against its expected value
(JSON or diagnostic notation), and re-encoded where the vector says a generic
encoder should reproduce the bytes.
-/

namespace Cborg.Tests.Reference

open Lean (Json JsonNumber)
open Term Diagnostic

def jsonInt (j : JsonNumber) : Option Int :=
  if j.exponent == 0 then some j.mantissa else none

partial def matchesJson : Term → Json → Bool
  | TInt n, .num j => jsonInt j == some n.toInt
  | TInteger n, .num j => jsonInt j == some n
  | THalf f, .num j | TFloat f, .num j => j.toFloat.toFloat32 == f
  | TDouble f, .num j => j.toFloat == f
  | TString s, .str s' => s == s'
  | TStringI ss, .str s' => String.join ss.toList == s'
  | TList ts, .arr js | TListI ts, .arr js =>
    ts.size == js.size && (ts.zip js).all fun (t, j) => matchesJson t j
  | TMap kvs, .obj o | TMapI kvs, .obj o =>
    kvs.size == o.size && kvs.all fun
      | (TString k, v) => match o.get? k with
        | some j => matchesJson v j
        | none => false
      | _ => false
  | TBool b, .bool b' => b == b'
  | TNull, .null => true
  | _, _ => false

structure Vector where
  hex : String
  roundtrip : Bool
  expected : Json ⊕ String

def loadVectors (path : System.FilePath) : IO (Array Vector) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let arr ← IO.ofExcept j.getArr?
  arr.mapM fun v => do
    let hex ← IO.ofExcept (v.getObjValAs? String "hex")
    let roundtrip ← IO.ofExcept (v.getObjValAs? Bool "roundtrip")
    let expected ← match v.getObjVal? "decoded", v.getObjValAs? String "diagnostic" with
      | .ok d, _ => pure (.inl d)
      | _, .ok s => pure (.inr s)
      | _, _ => throw (IO.userError s!"vector {hex} has no expected value")
    pure { hex, roundtrip, expected }

def externalVector (v : Vector) : TestM Unit := do
  let bs := unhex v.hex
  match decodeAll decodeTerm bs with
  | .error e => check s!"decode {v.hex}" false fun _ => e
  | .ok t =>
    match v.expected with
    | .inl j => check s!"decoded {v.hex}" (matchesJson t j) fun _ => s!"got {t}, want {j.compress}"
    | .inr d => checkEq s!"diagnostic {v.hex}" d (diagnosticNotation t)
    if v.roundtrip then
      checkEq s!"roundtrip {v.hex}" bs (toByteArray (encodeTerm t))

/-- The RFC 7049 examples with their diagnostic notation, as listed in Haskell cborg's tests. -/
def rfc7049TestVector : List (String × String) := [
  ("0", "00"),
  ("1", "01"),
  ("10", "0a"),
  ("23", "17"),
  ("24", "1818"),
  ("25", "1819"),
  ("100", "1864"),
  ("1000", "1903e8"),
  ("1000000", "1a000f4240"),
  ("1000000000000", "1b000000e8d4a51000"),
  ("18446744073709551615", "1bffffffffffffffff"),
  ("18446744073709551616", "c249010000000000000000"),
  ("-18446744073709551616", "3bffffffffffffffff"),
  ("-18446744073709551617", "c349010000000000000000"),
  ("-1", "20"),
  ("-10", "29"),
  ("-100", "3863"),
  ("-1000", "3903e7"),
  ("0.0", "f90000"),
  ("-0.0", "f98000"),
  ("1.0", "f93c00"),
  ("1.1", "fb3ff199999999999a"),
  ("1.5", "f93e00"),
  ("65504.0", "f97bff"),
  ("100000.0", "fa47c35000"),
  ("3.4028234663852886e+38", "fa7f7fffff"),
  ("1.0e+300", "fb7e37e43c8800759c"),
  ("5.960464477539063e-8", "f90001"),
  ("0.00006103515625", "f90400"),
  ("-4.0", "f9c400"),
  ("-4.1", "fbc010666666666666"),
  ("Infinity", "f97c00"),
  ("NaN", "f97e00"),
  ("-Infinity", "f9fc00"),
  ("Infinity", "fa7f800000"),
  ("-Infinity", "faff800000"),
  ("Infinity", "fb7ff0000000000000"),
  ("-Infinity", "fbfff0000000000000"),
  ("false", "f4"),
  ("true", "f5"),
  ("null", "f6"),
  ("undefined", "f7"),
  ("simple(16)", "f0"),
  ("simple(24)", "f818"),
  ("simple(255)", "f8ff"),
  ("0(\"2013-03-21T20:04:00Z\")", "c074323031332d30332d32315432303a30343a30305a"),
  ("1(1363896240)", "c11a514b67b0"),
  ("1(1363896240.5)", "c1fb41d452d9ec200000"),
  ("23(h'01020304')", "d74401020304"),
  ("24(h'6449455446')", "d818456449455446"),
  ("32(\"http://www.example.com\")", "d82076687474703a2f2f7777772e6578616d706c652e636f6d"),
  ("h''", "40"),
  ("h'01020304'", "4401020304"),
  ("\"\"", "60"),
  ("\"a\"", "6161"),
  ("\"IETF\"", "6449455446"),
  ("\"\\\"\\\\\"", "62225c"),
  ("\"ü\"", "62c3bc"),
  ("\"水\"", "63e6b0b4"),
  ("\"𐅑\"", "64f0908591"),
  ("[]", "80"),
  ("[1, 2, 3]", "83010203"),
  ("[1, [2, 3], [4, 5]]", "8301820203820405"),
  ("[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]", "98190102030405060708090a0b0c0d0e0f101112131415161718181819"),
  ("{}", "a0"),
  ("{1: 2, 3: 4}", "a201020304"),
  ("{\"a\": 1, \"b\": [2, 3]}", "a26161016162820203"),
  ("[\"a\", {\"b\": \"c\"}]", "826161a161626163"),
  ("{\"a\": \"A\", \"b\": \"B\", \"c\": \"C\", \"d\": \"D\", \"e\": \"E\"}", "a56161614161626142616361436164614461656145"),
  ("(_ h'0102', h'030405')", "5f42010243030405ff"),
  ("(_ \"strea\", \"ming\")", "7f657374726561646d696e67ff"),
  ("[_ ]", "9fff"),
  ("[_ 1, [2, 3], [_ 4, 5]]", "9f018202039f0405ffff"),
  ("[_ 1, [2, 3], [4, 5]]", "9f01820203820405ff"),
  ("[1, [2, 3], [_ 4, 5]]", "83018202039f0405ff"),
  ("[1, [_ 2, 3], [4, 5]]", "83019f0203ff820405"),
  ("[_ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]", "9f0102030405060708090a0b0c0d0e0f101112131415161718181819ff"),
  ("{_ \"a\": 1, \"b\": [_ 2, 3]}", "bf61610161629f0203ffff"),
  ("[\"a\", {_ \"b\": \"c\"}]", "826161bf61626163ff"),
  ("{_ \"Fun\": true, \"Amt\": -2}", "bf6346756ef563416d7421ff"),
]

def rfc7049Case (c : String × String) : TestM Unit := do
  let (diag, h) := c
  let bs := unhex h
  match decodeAll decodeTerm bs with
  | .error e => check s!"decode {h}" false fun _ => e
  | .ok t =>
    checkEq s!"diagnostic {h}" diag (diagnosticNotation t)
    checkEq s!"roundtrip {h}" bs (toByteArray (encodeTerm t))

def main : IO UInt32 := do
  let vs ← loadVectors "testdata/appendix_a.json"
  runSuite "Reference" do
    for v in vs do externalVector v
    for c in rfc7049TestVector do rfc7049Case c

end Cborg.Tests.Reference

def main : IO UInt32 := Cborg.Tests.Reference.main
