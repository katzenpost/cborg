-- SPDX-License-Identifier: GPL-3.0-or-later
-- Follows diagnosticNotation in Haskell cborg's tests/Tests/Reference/Implementation.hs
-- (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Term

/-!
# Cborg.Diagnostic

CBOR diagnostic notation (RFC 8949 §8) for `Term`, e.g. `{"a": [1, h'ff'], 1: 1.5}`.
-/

namespace Cborg.Diagnostic

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexBytes (bs : ByteArray) : String :=
  bs.foldl (fun s b => s.push (hexDigit (b.toNat / 16)) |>.push (hexDigit (b.toNat % 16))) ""

def showBytes (bs : ByteArray) : String := s!"h'{hexBytes bs}'"

def showString (s : String) : String :=
  let body := s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c.toNat < 0x20 then
      let n := c.toNat
      acc ++ "\\u00" ++ String.singleton (hexDigit (n / 16)) ++ String.singleton (hexDigit (n % 16))
    else acc.push c) ""
  "\"" ++ body ++ "\""

/-- A finite positive double as `mant * 2^ex`, exactly. -/
private def ratParts (f : Float) : Nat × Int :=
  let bits := f.toBits
  let exp := ((bits >>> 52) &&& 0x7ff).toNat
  let frac := (bits &&& 0xfffffffffffff).toNat
  if exp == 0 then (frac, -1074) else (frac + 2 ^ 52, (exp : Int) - 1075)

/-- `|f|` to `k` significant figures as `(m, e)`: `m` has `k` digits and `e` is the exponent of the first. -/
private def digitsOf (f : Float) (k : Nat) : Nat × Int :=
  let (mant, ex) := ratParts f
  let round (e : Int) : Nat :=
    let s := e - k + 1
    let num := mant * 2 ^ ex.toNat * 10 ^ (-s).toNat
    let den := 2 ^ (-ex).toNat * 10 ^ s.toNat
    (2 * num + den) / (2 * den)
  -- the floating-point estimate of the exponent can be off by one either way
  let e0 : Int := (Float.floor (Float.log10 f)).toInt64.toInt
  let e := if round e0 ≥ 10 ^ k then e0 + 1 else if round e0 < 10 ^ (k - 1) then e0 - 1 else e0
  let m := round e
  if m ≥ 10 ^ k then (m / 10, e + 1) else (m, e)

/-- The double nearest to `m * 10^(e - k + 1)`. -/
private def readBack (m : Nat) (k : Nat) (e : Int) : Float :=
  let x : Int := e - k + 1
  if x ≥ 0 then Float.ofScientific m false x.toNat else Float.ofScientific m true (-x).toNat

private def take (s : String) (n : Nat) : String := String.ofList (s.toList.take n)
private def drop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- Shortest decimal that reads back as the same double. -/
def showFloat (f : Float) : String :=
  if f.isNaN then "NaN"
  else if f.isInf then (if f > 0 then "Infinity" else "-Infinity")
  else if f == 0 then (if f.toBits >>> 63 == 1 then "-0.0" else "0.0")
  else
    let sign := if f < 0 then "-" else ""
    let a := f.abs
    let (m, e) := (List.range 17).foldr (fun i acc =>
      let k := i + 1
      let (m, e) := digitsOf a k
      if readBack m k e == a then (m, e) else acc) (digitsOf a 17)
    let ds := String.ofList ((toString m).toList.reverse.dropWhile (· == '0')).reverse
    let ds := if ds.isEmpty then "0" else ds
    let n := ds.length
    let body :=
      if -5 ≤ e ∧ e < 16 then
        if e < 0 then "0." ++ "".pushn '0' (-e - 1).toNat ++ ds
        else if e.toNat + 1 ≥ n then ds ++ "".pushn '0' (e.toNat + 1 - n) ++ ".0"
        else take ds (e.toNat + 1) ++ "." ++ drop ds (e.toNat + 1)
      else
        let mant := if n == 1 then ds ++ ".0" else take ds 1 ++ "." ++ drop ds 1
        mant ++ "e" ++ (if e ≥ 0 then "+" else "-") ++ toString e.natAbs
    sign ++ body

open Term in
partial def diagnosticNotation : Term → String
  | TInt n => toString n
  | TInteger n => toString n
  | TBytes bs => showBytes bs
  | TBytesI bss => "(_ " ++ ", ".intercalate (bss.toList.map showBytes) ++ ")"
  | TString s => showString s
  | TStringI ss => "(_ " ++ ", ".intercalate (ss.toList.map showString) ++ ")"
  | TList ts => "[" ++ ", ".intercalate (ts.toList.map diagnosticNotation) ++ "]"
  | TListI ts => "[_ " ++ ", ".intercalate (ts.toList.map diagnosticNotation) ++ "]"
  | TMap kvs => "{" ++ ", ".intercalate (kvs.toList.map showPair) ++ "}"
  | TMapI kvs => "{_ " ++ ", ".intercalate (kvs.toList.map showPair) ++ "}"
  | TTagged tag t => s!"{tag}({diagnosticNotation t})"
  | TBool b => if b then "true" else "false"
  | TNull => "null"
  | TSimple 20 => "false"
  | TSimple 21 => "true"
  | TSimple 22 => "null"
  | TSimple 23 => "undefined"
  | TSimple w => s!"simple({w})"
  | THalf f | TFloat f => showFloat f.toFloat
  | TDouble f => showFloat f
where
  showPair : Term × Term → String
    | (k, v) => diagnosticNotation k ++ ": " ++ diagnosticNotation v

instance : ToString Term := ⟨diagnosticNotation⟩

end Cborg.Diagnostic
