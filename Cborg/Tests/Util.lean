-- SPDX-License-Identifier: GPL-3.0-or-later

import Cborg

/-!
# Test helpers

A minimal runner: `check` records a failure without stopping, and `runSuite`
prints a summary and returns a non-zero exit code if anything failed.
-/

namespace Cborg.Tests

abbrev TestM := StateT (Nat × Nat) IO

def check (name : String) (ok : Bool) (detail : Unit → String := fun _ => "") : TestM Unit := do
  let (pass, fail) ← get
  if ok then set (pass + 1, fail)
  else
    set (pass, fail + 1)
    let d := detail ()
    IO.println s!"FAIL {name}{if d.isEmpty then "" else ": " ++ d}"

def checkEq {α : Type} [BEq α] [ToString α] (name : String) (expected actual : α) : TestM Unit :=
  check name (expected == actual) fun _ => s!"expected {expected}, got {actual}"

def runSuite (name : String) (t : TestM Unit) : IO UInt32 := do
  let ((), (pass, fail)) ← t.run (0, 0)
  IO.println s!"{name}: {pass} passed, {fail} failed"
  return if fail == 0 then 0 else 1

def hex (bs : ByteArray) : String := Diagnostic.hexBytes bs

def unhex (s : String) : ByteArray := Id.run do
  let digit (c : Char) : UInt8 :=
    if c.isDigit then (c.toNat - 48).toUInt8
    else if 'a' ≤ c && c ≤ 'f' then (c.toNat - 87).toUInt8
    else (c.toNat - 55).toUInt8
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size/2] do
    out := out.push (digit cs[2*i]! * 16 + digit cs[2*i+1]!)
  return out

instance : BEq ByteArray := ⟨fun a b => a.data == b.data⟩
instance : ToString ByteArray := ⟨hex⟩

/-- Decode exactly one value, failing on trailing bytes. -/
def decodeAll {α : Type} (d : Decoder α) (bs : ByteArray) : Except String α :=
  match deserialiseFromBytes d bs with
  | .ok (rest, a) => if rest.size == 0 then .ok a else .error s!"trailing bytes: {hex rest}"
  | .error e => .error (toString e)

end Cborg.Tests
