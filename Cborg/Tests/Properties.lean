-- SPDX-License-Identifier: GPL-3.0-or-later
-- Follows Haskell cborg tests/Tests/{Properties,Canonical,Boundary,UTF8,ByteOffset,ByteSpan}.hs
-- (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Tests.Util

/-!
# Randomised properties

A seeded generator stands in for QuickCheck. Every run uses the same seeds, so
a failure reproduces; the seed is printed with it.
-/

namespace Cborg.Tests.Properties

open Term

abbrev Gen := StateM StdGen

def nat (lo hi : Nat) : Gen Nat := modifyGet fun g => randNat g lo hi
def bool : Gen Bool := (· == 1) <$> nat 0 1
def pick {α : Type} [Inhabited α] (xs : Array α) : Gen α := do return xs[← nat 0 (xs.size - 1)]!

/-- A `UInt64` whose bit length is uniform, so every header width turns up. -/
def word64 : Gen UInt64 := do
  let bits ← nat 0 64
  if bits == 0 then return 0
  return (← nat (2 ^ (bits - 1)) (2 ^ bits - 1)).toUInt64

def int64 : Gen Int64 := do
  let w ← word64
  let w := w >>> 1
  return if ← bool then w.toInt64 else -1 - w.toInt64

def bytes (maxLen : Nat) : Gen ByteArray := do
  let n ← nat 0 maxLen
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do out := out.push (← nat 0 255).toUInt8
  return out

def char : Gen Char := do
  let ranges : Array (Nat × Nat) := #[(0x20, 0x7e), (0, 0x1f), (0x80, 0x7ff), (0x800, 0xd7ff),
    (0xe000, 0xffff), (0x10000, 0x10ffff)]
  let (lo, hi) ← pick ranges
  return Char.ofNat (← nat lo hi)

def string (maxLen : Nat) : Gen String := do
  let n ← nat 0 maxLen
  let mut s := ""
  for _ in [0:n] do s := s.push (← char)
  return s

def nonNaN32 : Gen Float32 := do
  let f := Float32.ofBits (← nat 0 0xffffffff).toUInt32
  return if f.isNaN then 1.5 else f

def nonNaN64 : Gen Float := do
  let f := Float.ofBits (← nat 0 0xffffffffffffffff).toUInt64
  return if f.isNaN then -2.25 else f

def half : Gen Float32 := do
  let f := Magic.wordToFloat16 (← nat 0 0xffff).toUInt16
  return if f.isNaN then 0.5 else f

def listOf {α : Type} (n : Nat) (g : Gen α) : Gen (Array α) := do
  let k ← nat 0 n
  let mut out := #[]
  for _ in [0:k] do out := out.push (← g)
  return out

/--
A random term in the shape `decodeTerm` produces: integers that fit `Int64` are
`TInt`, tags 2 and 3 (bignums) and the simple values for false, true and null
are avoided, and floats are never NaN, whose payload encoding canonicalises.
-/
partial def term (depth : Nat) : Gen Term := do
  let leaf := depth == 0
  match ← nat 0 (if leaf then 9 else 20) with
  | 0 => return TInt (← int64)
  | 1 =>
    let n ← nat (2 ^ 63) (2 ^ 70)
    return TInteger (if ← bool then n else -1 - (n : Int))
  | 2 => return TBytes (← bytes 40)
  | 3 => return TString (← string 20)
  | 4 => return TBool (← bool)
  | 5 => return TNull
  | 6 => return TSimple (← pick #[0, 7, 16, 19, 23, 24, 31, 32, 100, 255])
  | 7 => return THalf (← half)
  | 8 => return TFloat (← nonNaN32)
  | 9 => return TDouble (← nonNaN64)
  | 10 => return TBytesI (← listOf 4 (bytes 10))
  | 11 => return TStringI (← listOf 4 (string 6))
  | 12 | 15 | 16 | 17 =>
    let ts ← listOf 5 (term (depth - 1))
    return if ← bool then TList ts else TListI ts
  | 13 | 18 | 19 =>
    let kvs ← listOf 5 (do return (← term (depth - 1), ← term (depth - 1)))
    return if ← bool then TMap kvs else TMapI kvs
  | _ =>
    let tag ← word64
    let tag := if tag == 2 || tag == 3 then 4 else tag
    return TTagged tag (← term (depth - 1))

/-- Split bytes into random chunks, possibly empty ones. -/
def chunks (bs : ByteArray) : Gen (List ByteArray) := do
  let mut out := #[]
  let mut pos := 0
  while pos < bs.size do
    let n ← nat 0 (min 12 (bs.size - pos))
    out := out.push (bs.extract pos (pos + n))
    pos := pos + n
  return out.toList

/-- Feed chunks to an incremental decode, then signal end of input. -/
def feed {α : Type} : IDecode α → List ByteArray → IDecode α
  | .Partial k, c :: cs => feed (k (some c)) cs
  | .Partial k, [] => k none
  | r, _ => r

def incremental {α : Type} (d : Decoder α) (cs : List ByteArray) : Except String (α × Nat) :=
  match feed (deserialiseIncremental d) cs with
  | .Done rest off a => if rest.size == 0 then .ok (a, off) else .error "trailing bytes"
  | .Fail _ _ e => .error (toString e)
  | .Partial _ => .error "still partial"

/-- Run `n` cases of a property, each from its own seed. -/
def forAll (name : String) (n : Nat) (prop : Gen (Option String)) : TestM Unit := do
  let mut failed := false
  for seed in [0:n] do
    if failed then break
    match (prop.run (mkStdGen seed)).1 with
    | none => pure ()
    | some msg =>
      failed := true
      check name false fun _ => s!"seed {seed}: {msg}"
  if !failed then check name true

def termRoundTrip : Gen (Option String) := do
  let t ← term 4
  let bs := toByteArray (encodeTerm t)
  match decodeAll decodeTerm bs with
  | .error e => return some s!"{t}: {e}"
  | .ok t' => return if t' == t then none else some s!"{t} decoded as {t'}"

def termFlat : Gen (Option String) := do
  let t ← term 4
  let ft := toFlatTerm (encodeTerm t)
  if !validFlatTerm ft then return some s!"{t}: invalid flat term"
  match fromFlatTerm decodeTerm ft with
  | .error e => return some s!"{t}: {e}"
  | .ok t' => return if t' == t then none else some s!"{t} came back as {t'}"

def tokensMatchBytes : Gen (Option String) := do
  let t ← term 4
  let e := encodeTerm t
  let fromBytes := decodePreEncoded (toByteArray e)
  return if fromBytes == toFlatTerm e then none else some s!"{t}: token streams differ"

def termIncremental : Gen (Option String) := do
  let t ← term 4
  let bs := toByteArray (encodeTerm t)
  match incremental decodeTerm (← chunks bs) with
  | .error e => return some s!"{t}: {e}"
  | .ok (t', off) =>
    return if t' == t && off == bs.size then none else some s!"{t}: got {t'} at offset {off}"

def truncatedFails : Gen (Option String) := do
  let t ← term 3
  let bs := toByteArray (encodeTerm t)
  let cut ← nat 0 (bs.size - 1)
  match deserialiseFromBytes decodeTerm (bs.extract 0 cut) with
  | .ok _ => return some s!"{t}: decoded from {cut} of {bs.size} bytes"
  | .error e => return if e.msg == "end of input" then none else some s!"{t}: {e}"

def truncatedIncrementalFails : Gen (Option String) := do
  let t ← term 3
  let bs := toByteArray (encodeTerm t)
  let cut ← nat 0 (bs.size - 1)
  match incremental decodeTerm (← chunks (bs.extract 0 cut)) with
  | .ok _ => return some s!"{t}: decoded from {cut} of {bs.size} bytes"
  | .error e => return if e.endsWith "end of input" then none else some s!"{t}: {e}"

/-- A header for major type `mt` with argument `w`, of a given total size (1, 2, 3, 5 or 9). -/
def header (mt : UInt8) (w : UInt64) (sz : Nat) : ByteArray :=
  let ib := mt <<< 5
  match sz with
  | 1 => ByteArray.mk #[ib ||| w.toUInt8]
  | 2 => ByteArray.mk #[ib ||| 24, w.toUInt8]
  | 3 => Magic.pushWord16 (ByteArray.mk #[ib ||| 25]) w.toUInt16
  | 5 => Magic.pushWord32 (ByteArray.mk #[ib ||| 26]) w.toUInt32
  | _ => Magic.pushWord64 (ByteArray.mk #[ib ||| 27]) w

def minimalSize (w : UInt64) : Nat :=
  if w < 24 then 1 else if w < 0x100 then 2 else if w < 0x10000 then 3
  else if w < 0x100000000 then 5 else 9

/-- A random header for `w` that may be longer than it needs to be. -/
def anyHeader (mt : UInt8) (w : UInt64) : Gen (ByteArray × Bool) := do
  let sizes := #[1, 2, 3, 5, 9].filter (· ≥ minimalSize w)
  let sz ← pick sizes
  return (header mt w sz, sz == minimalSize w)

/--
For one major type: the plain decoder accepts every header width, the canonical
decoder accepts exactly the minimal one, and both agree on the value.
-/
def canonicalProp {α : Type} [BEq α] [ToString α] (mt : UInt8) (gen : Gen UInt64)
    (plain canon : Decoder α) (expect : UInt64 → α) : Gen (Option String) := do
  let w ← gen
  let (bs, minimal) ← anyHeader mt w
  match decodeAll plain bs, decodeAll canon bs with
  | .ok a, .ok b =>
    if !minimal then return some s!"{hex bs}: canonical decoder accepted it"
    return if a == expect w && b == expect w then none else some s!"{hex bs}: got {a} and {b}"
  | .ok a, .error _ =>
    if minimal then return some s!"{hex bs}: canonical decoder rejected it"
    return if a == expect w then none else some s!"{hex bs}: got {a}"
  | .error e, _ => return some s!"{hex bs}: {e}"

def wordIn (hi : UInt64) : Gen UInt64 := do
  let w ← word64
  return if w ≤ hi then w else w % (hi + 1)

def canonicalTests : TestM Unit := do
  forAll "canonical Word" 2000 <| canonicalProp 0 word64 decodeWord decodeWordCanonical id
  forAll "canonical Word8" 2000 <|
    canonicalProp 0 (wordIn 0xff) decodeWord8 decodeWord8Canonical (·.toUInt8)
  forAll "canonical Word16" 2000 <|
    canonicalProp 0 (wordIn 0xffff) decodeWord16 decodeWord16Canonical (·.toUInt16)
  forAll "canonical Word32" 2000 <|
    canonicalProp 0 (wordIn 0xffffffff) decodeWord32 decodeWord32Canonical (·.toUInt32)
  forAll "canonical NegWord" 2000 <| canonicalProp 1 word64 decodeNegWord decodeNegWordCanonical id
  forAll "canonical Int (positive)" 2000 <|
    canonicalProp 0 (wordIn 0x7fffffffffffffff) decodeInt decodeIntCanonical (·.toInt64)
  forAll "canonical Int (negative)" 2000 <|
    canonicalProp 1 (wordIn 0x7fffffffffffffff) decodeInt decodeIntCanonical (-1 - ·.toInt64)
  forAll "canonical Int8" 2000 <|
    canonicalProp 1 (wordIn 0x7f) decodeInt8 decodeInt8Canonical (-1 - ·.toInt64.toInt8)
  forAll "canonical Int16" 2000 <|
    canonicalProp 0 (wordIn 0x7fff) decodeInt16 decodeInt16Canonical (·.toInt64.toInt16)
  forAll "canonical Int32" 2000 <|
    canonicalProp 1 (wordIn 0x7fffffff) decodeInt32 decodeInt32Canonical (-1 - ·.toInt64.toInt32)
  forAll "canonical Integer" 2000 <|
    canonicalProp 1 word64 decodeInteger decodeIntegerCanonical (-1 - ·.toNat)
  forAll "canonical ListLen" 2000 <|
    canonicalProp 4 (wordIn 0x7fffffffffffffff) decodeListLen decodeListLenCanonical (·.toNat)
  forAll "canonical MapLen" 2000 <|
    canonicalProp 5 (wordIn 0x7fffffffffffffff) decodeMapLen decodeMapLenCanonical (·.toNat)
  forAll "canonical Tag" 2000 <| canonicalProp 6 word64 decodeTag decodeTagCanonical id
  forAll "canonical bytes length" 2000 do
    let b ← bytes 300
    let (hdr, minimal) ← anyHeader 2 b.size.toUInt64
    let bs := hdr ++ b
    match decodeAll decodeBytes bs, decodeAll decodeBytesCanonical bs with
    | .ok a, .ok _ => return if minimal && a == b then none else some s!"{hex bs}"
    | .ok a, .error _ => return if !minimal && a == b then none else some s!"{hex bs}"
    | .error e, _ => return some e
  forAll "canonical string length" 2000 do
    let s ← string 100
    let (hdr, minimal) ← anyHeader 3 s.utf8ByteSize.toUInt64
    let bs := hdr ++ s.toUTF8
    match decodeAll decodeString bs, decodeAll decodeStringCanonical bs with
    | .ok a, .ok _ => return if minimal && a == s then none else some s!"{hex bs}"
    | .ok a, .error _ => return if !minimal && a == s then none else some s!"{hex bs}"
    | .error e, _ => return some e
  forAll "canonical simple" 300 do
    let w ← nat 0 255
    let long ← bool
    if w ≥ 24 && !long || w ∈ [20, 21, 22, 23] then return none
    let bs := if long then ByteArray.mk #[0xf8, w.toUInt8] else ByteArray.mk #[0xe0 + w.toUInt8]
    let canonical := !long || w ≥ 24
    match decodeAll decodeSimple bs, decodeAll decodeSimpleCanonical bs with
    | .ok a, .ok _ => return if canonical && a.toNat == w then none else some (hex bs)
    | .ok a, .error _ => return if !canonical && a.toNat == w then none else some (hex bs)
    | .error e, _ => return some e
  -- a float decodes canonically only at its own width; NaN only as f97e00
  forAll "canonical floats" 2000 do
    let h := Magic.wordToFloat16 (← nat 0 0xffff).toUInt16
    let f32 ← nonNaN32
    let encodings : List (ByteArray × Nat) := [
      (Magic.pushWord16 (ByteArray.mk #[0xf9]) (Magic.floatToWord16 h), 2),
      (Magic.pushWord32 (ByteArray.mk #[0xfa]) f32.toBits, 4),
      (Magic.pushWord64 (ByteArray.mk #[0xfb]) f32.toFloat.toBits, 8)]
    for (bs, width) in encodings do
      let nanOk := (decodeAll decodeFloat16Canonical bs).toOption.map Float32.isNaN
      let ok16 := (decodeAll decodeFloat16Canonical bs).toBool
      let ok32 := (decodeAll decodeFloatCanonical bs).toBool
      let ok64 := (decodeAll decodeDoubleCanonical bs).toBool
      let isNaN := width == 2 && h.isNaN
      let expect := if isNaN then (hex bs == "f97e00", false, false)
        else (width == 2, width == 4, width == 8)
      let expect := if isNaN then (expect.1, expect.1, expect.1) else expect
      if (ok16, ok32, ok64) != expect then
        return some s!"{hex bs}: canonical accepted {(ok16, ok32, ok64)}, nan {nanOk}"
    return none

/-- Values just inside and outside each decoder's range. -/
def boundaryTests : TestM Unit := do
  let wordCase {α : Type} (name : String) (hi : Nat) (d dc : Decoder α) : TestM Unit :=
    forAll s!"boundary {name}" 1000 do
      let n ← pick #[0, 1, hi - 1, hi, hi + 1, hi + 2, 2 ^ 64 - 1, ← nat 0 (2 ^ 64 - 1)]
      let n := min n (2 ^ 64 - 1)
      let bs := toByteArray (encodeWord64 n.toUInt64)
      let inside := decide (n ≤ hi)
      let r := ((decodeAll d bs).toBool, (decodeAll dc bs).toBool)
      return if r == (inside, inside) then none else some s!"{n}: {r}"
  wordCase "Word8" 0xff decodeWord8 decodeWord8Canonical
  wordCase "Word16" 0xffff decodeWord16 decodeWord16Canonical
  wordCase "Word32" 0xffffffff decodeWord32 decodeWord32Canonical
  wordCase "Word64" (2 ^ 64 - 1) decodeWord64 decodeWord64Canonical
  let intCase {α : Type} (name : String) (lo hi : Int) (d dc : Decoder α) : TestM Unit :=
    forAll s!"boundary {name}" 1000 do
      let r ← nat 0 (2 ^ 65 - 1)
      let n ← pick #[lo - 1, lo, lo + 1, hi - 1, hi, hi + 1, -(2 ^ 64), 2 ^ 64 - 1,
        (r : Int) - 2 ^ 64]
      let bs := toByteArray (encodeInteger n)
      let inside := decide (lo ≤ n ∧ n ≤ hi)
      let res := ((decodeAll d bs).toBool, (decodeAll dc bs).toBool)
      return if res == (inside, inside) then none else some s!"{n}: {res}"
  intCase "Int8" (-0x80) 0x7f decodeInt8 decodeInt8Canonical
  intCase "Int16" (-0x8000) 0x7fff decodeInt16 decodeInt16Canonical
  intCase "Int32" (-0x80000000) 0x7fffffff decodeInt32 decodeInt32Canonical
  intCase "Int64" (-0x8000000000000000) 0x7fffffffffffffff decodeInt64 decodeInt64Canonical
  forAll "boundary ListLen" 1000 do
    let n ← pick #[0, 0x7fffffffffffffff, 0x8000000000000000, ← word64]
    let bs := toByteArray (encodeListLen n)
    let inside := n ≤ 0x7fffffffffffffff
    return if (decodeAll decodeListLen bs).toBool == inside then none else some s!"{n}"

/-- Byte strings are UTF-8 checked exactly when decoded as text. -/
def utf8Tests : TestM Unit := do
  let invalid := ["80", "c080", "c1bf", "e080af", "eda080", "edbfbf", "f4908080", "f88080808080",
    "e282", "ff", "61c3"]
  for h in invalid do
    let bs := header 3 (h.length / 2).toUInt64 (minimalSize (h.length / 2).toUInt64) ++ unhex h
    check s!"invalid UTF-8 {h}" (!(decodeAll decodeString bs).toBool)
    check s!"raw UTF-8 bytes {h}" ((decodeAll decodeUtf8ByteArray bs).toOption == some (unhex h))
  forAll "random text round trip" 1000 do
    let s ← string 50
    match decodeAll decodeString (toByteArray (encodeString s)) with
    | .ok s' => return if s == s' then none else some s!"{s.quote}"
    | .error e => return some e

/-- Spans and offsets of several items decoded one after another, whole and chunked. -/
def spanTests : TestM Unit := do
  let decoder (n : Nat) : Decoder (Array (Term × ByteSpan × ByteOffset × ByteOffset)) := do
    let mut out := #[]
    for _ in [0:n] do
      let ((t, span), before, after) ← decodeWithByteOffsets (decodeWithByteSpan decodeTerm)
      out := out.push (t, span, before, after)
    return out
  let checkSpans (ts : Array Term) (r : Array (Term × ByteSpan × ByteOffset × ByteOffset)) :
      Option String := Id.run do
    let mut off := 0
    for (t, (t', span, before, after)) in ts.zip r do
      let bs := toByteArray (encodeTerm t)
      if !(t == t' && span == bs && before == off && after == off + bs.size) then
        return some s!"{t}: span {hex span} [{before}, {after}) expected {hex bs} at {off}"
      off := off + bs.size
    return none
  forAll "byte spans and offsets" 500 do
    let ts ← listOf 6 (term 3)
    let bs := ts.foldl (fun acc t => acc ++ toByteArray (encodeTerm t)) .empty
    match decodeAll (decoder ts.size) bs with
    | .error e => return some e
    | .ok r => return checkSpans ts r
  forAll "byte spans and offsets, chunked" 500 do
    let ts ← listOf 6 (term 3)
    let bs := ts.foldl (fun acc t => acc ++ toByteArray (encodeTerm t)) .empty
    match incremental (decoder ts.size) (← chunks bs) with
    | .error e => return some e
    | .ok (r, _) => return checkSpans ts r
  -- nested spans see their own bytes
  let nested : Decoder (ByteSpan × ByteSpan) := do
    openByteSpan
    let _ ← decodeListLen
    let (_, inner) ← decodeWithByteSpan decodeWord
    let outer ← peekByteSpan
    closeByteSpan
    return (inner, outer)
  match decodeAll nested (unhex "8218ff") with
  | .ok (inner, outer) =>
    checkEq "nested span inner" "18ff" (hex inner)
    checkEq "nested span outer" "8218ff" (hex outer)
  | .error e => check "nested spans" false fun _ => e

def main : IO UInt32 :=
  runSuite "Properties" do
    forAll "term round trip" 3000 termRoundTrip
    forAll "term via flat term" 3000 termFlat
    forAll "token stream from bytes" 1000 tokensMatchBytes
    forAll "term incremental" 3000 termIncremental
    forAll "truncated input" 1000 truncatedFails
    forAll "truncated input, chunked" 1000 truncatedIncrementalFails
    canonicalTests
    boundaryTests
    utf8Tests
    spanTests

end Cborg.Tests.Properties

def main : IO UInt32 := Cborg.Tests.Properties.main
