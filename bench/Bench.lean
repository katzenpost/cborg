-- SPDX-License-Identifier: GPL-3.0-or-later

import Cborg
import LeanBench

/-!
# Benchmarks

Encoding and decoding at geometrically growing sizes, up to the thin client's
40 MiB frame limit. Linear code grows about 4× per row of byte strings and
about 4× per row of item counts.

    lake exe cborg-bench --where "name(/decode bytes/)"
-/

open Cborg

def cfg : LeanBench.BenchConfig := { suite := some "cborg", samples := 5, warmup := 1 }

def sizes : List (String × Nat) :=
  [("16KiB", 16 * 1024), ("256KiB", 256 * 1024), ("4MiB", 4 * 1024 * 1024),
   ("40MiB", 40 * 1024 * 1024)]

def counts : List (String × Nat) := [("1k", 1000), ("4k", 4000), ("16k", 16000), ("64k", 64000)]

def payload (n : Nat) : ByteArray := ByteArray.mk (Array.ofFn fun (i : Fin n) => (i.val * 7 % 251).toUInt8)

/-- Feed `bs` to an incremental decode in chunks of `chunk` bytes. -/
partial def feedChunks {α : Type} (bs : ByteArray) (chunk : Nat) (pos : Nat) : IDecode α → Option α
  | .Partial k =>
    if pos ≥ bs.size then feedChunks bs chunk pos (k none)
    else feedChunks bs chunk (pos + chunk) (k (some (bs.extract pos (pos + chunk))))
  | .Done _ _ a => some a
  | .Fail _ _ _ => none

def benches : IO (Array LeanBench.Bench) := do
  let out ← IO.mkRef (0 : Nat)
  let mut bs := #[]
  for (label, n) in sizes do
    let raw ← IO.mkRef (payload n)
    let enc ← IO.mkRef (toByteArray (encodeBytes (payload n)))
    -- a thin client response: a map with a large payload field among small ones
    let frame ← IO.mkRef (toByteArray (encodeMapLen 3 ++ encodeString "query_id" ++ encodeBytes (payload 16)
      ++ encodeString "payload" ++ encodeBytes (payload n) ++ encodeString "epoch" ++ encodeWord64 5))
    bs := bs ++ #[
      { name := s!"encode bytes {label}", config := cfg,
        action := do out.set (toByteArray (encodeBytes (← raw.get))).size },
      { name := s!"decode bytes {label}", config := cfg,
        action := do
          match deserialiseFromBytes decodeBytes (← enc.get) with
          | .ok (_, b) => out.set b.size
          | .error _ => out.set 0 },
      { name := s!"decode record {label}", config := cfg,
        action := do
          match deserialiseFromBytes decodeRecord (← frame.get) with
          | .ok (_, r) => out.set r.fields.size
          | .error _ => out.set 0 },
      { name := s!"decode bytes incremental 64KiB chunks {label}", config := cfg,
        action := do
          let r := feedChunks (← enc.get) 65536 0 (deserialiseIncremental decodeBytes)
          out.set (r.map ByteArray.size |>.getD 0) }]
  for (label, n) in counts do
    let t : Term := .TList ((Array.range n).map fun i =>
      .TMap #[(.TString "id", .TInt i.toInt64), (.TString "v", .TBytes (payload 8))])
    let term ← IO.mkRef t
    let enc ← IO.mkRef (toByteArray (encodeTerm t))
    bs := bs ++ #[
      { name := s!"encode term {label} items", config := cfg,
        action := do out.set (toByteArray (encodeTerm (← term.get))).size },
      { name := s!"decode term {label} items", config := cfg,
        action := do
          match deserialiseFromBytes decodeTerm (← enc.get) with
          | .ok (_, .TList ts) => out.set ts.size
          | _ => out.set 0 }]
  return bs

def main (args : List String) : IO UInt32 := do
  (← benches).forM LeanBench.register
  LeanBench.runMain args
