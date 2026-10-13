-- SPDX-License-Identifier: GPL-3.0-or-later
-- Ported from Haskell cborg Codec/CBOR/Pretty.hs (BSD-3-Clause, see LICENSE.cborg).

import Cborg.Write
import Cborg.Diagnostic

/-!
# Cborg.Pretty

An annotated hex dump of an `Encoding`, in the style of cbor.me:

```
83  # list(3)
   f5  # bool(true)
   9f  # list(*)
      01  # word(1)
      ff  # break
   ...
```
-/

namespace Cborg.Pretty

open Tokens

structure PPState where
  toks : Tokens
  ind : Nat
  out : String

abbrev PP := StateT PPState (Except String)

def indent : PP Unit := modify fun s => { s with out := s.out.pushn ' ' s.ind }
def nl : PP Unit := modify fun s => { s with out := s.out.push '\n' }
def inc (i : Nat) : PP Unit := modify fun s => { s with ind := s.ind + i }
def dec (i : Nat) : PP Unit := modify fun s => { s with ind := s.ind - i }
def str (t : String) : PP Unit := modify fun s => { s with out := s.out ++ t }
def parens (t : String) : PP Unit := str s!"({t})"

/-- Split off the first token, as a one-token stream. -/
def unconsToken : Tokens → Option (Tokens × Tokens)
  | TkEnd => none
  | TkWord w ts => some (TkWord w TkEnd, ts)
  | TkInt n ts => some (TkInt n TkEnd, ts)
  | TkBytes bs ts => some (TkBytes bs TkEnd, ts)
  | TkBytesBegin ts => some (TkBytesBegin TkEnd, ts)
  | TkString s ts => some (TkString s TkEnd, ts)
  | TkUtf8ByteArray bs ts => some (TkUtf8ByteArray bs TkEnd, ts)
  | TkStringBegin ts => some (TkStringBegin TkEnd, ts)
  | TkListLen n ts => some (TkListLen n TkEnd, ts)
  | TkListBegin ts => some (TkListBegin TkEnd, ts)
  | TkMapLen n ts => some (TkMapLen n TkEnd, ts)
  | TkMapBegin ts => some (TkMapBegin TkEnd, ts)
  | TkTag w ts => some (TkTag w TkEnd, ts)
  | TkInteger n ts => some (TkInteger n TkEnd, ts)
  | TkNull ts => some (TkNull TkEnd, ts)
  | TkUndef ts => some (TkUndef TkEnd, ts)
  | TkBool b ts => some (TkBool b TkEnd, ts)
  | TkSimple w ts => some (TkSimple w TkEnd, ts)
  | TkFloat16 f ts => some (TkFloat16 f TkEnd, ts)
  | TkFloat32 f ts => some (TkFloat32 f TkEnd, ts)
  | TkFloat64 f ts => some (TkFloat64 f TkEnd, ts)
  | TkBreak ts => some (TkBreak TkEnd, ts)
  | TkEncoded bs ts => some (TkEncoded bs TkEnd, ts)

def getTerm : PP Tokens := do
  match unconsToken (← get).toks with
  | some (tk, rest) => modify (fun s => { s with toks := rest }); pure tk
  | none => throw "getTok: Unexpected end of input"

def peekTerm : PP Tokens := do
  match unconsToken (← get).toks with
  | some (tk, _) => pure tk
  | none => throw "peekTerm: Unexpected end of input"

def hexBS (bs : ByteArray) : String :=
  bs.foldl (fun s b => s ++ Diagnostic.hexBytes (ByteArray.mk #[b]) ++ " ") ""

/-- The bytes of one token, sixteen to a line. -/
partial def hexRep (tk : Tokens) : PP Unit :=
  go (writeTokens .empty tk)
where
  go (bs : ByteArray) : PP Unit := do
    indent
    if bs.size > 16 then
      str (hexBS (bs.extract 0 16)); nl; go (bs.extract 16 bs.size)
    else str (hexBS bs)

mutual

partial def pprint : PP Unit := do
  nl
  let term ← getTerm
  hexRep term
  str " "
  match term with
  | TkInt i _ => str "# int"; parens (toString i)
  | TkInteger i _ => str "# integer"; parens (toString i)
  | TkWord w _ => str "# word"; parens (toString w)
  | TkBytes bs _ => str "# bytes"; parens (toString bs.size)
  | TkBytesBegin _ => str "# bytes(*)"; inc 3; indef pprint
  | TkUtf8ByteArray bs _ => str "# text"; parens (toString bs.size)
  | TkString t _ => str "# text"; parens (Diagnostic.showString t)
  | TkStringBegin _ => str "# text(*)"; inc 3; indef pprint
  | TkListLen n _ =>
    str "# list"; parens (toString n)
    inc 3
    for _ in [0:n.toNat] do pprint
    dec 3
  | TkListBegin _ => str "# list(*)"; inc 3; indef pprint
  | TkMapLen n _ =>
    str "# map"; parens (toString n)
    for _ in [0:n.toNat] do ppMapPairs
  | TkMapBegin _ => str "# map(*)"; inc 3; indef ppMapPairs
  | TkBreak _ => str "# break"
  | TkTag w _ => str "# tag"; parens (toString w); inc 3; pprint; dec 3
  | TkBool b _ => str "# bool"; parens (if b then "true" else "false")
  | TkNull _ => str "# null"
  | TkUndef _ => str "# undefined"
  | TkSimple w _ => str "# simple"; parens (toString w)
  | TkFloat16 f _ => str "# float16"; parens (Diagnostic.showFloat f.toFloat)
  | TkFloat32 f _ => str "# float32"; parens (Diagnostic.showFloat f.toFloat)
  | TkFloat64 f _ => str "# float64"; parens (Diagnostic.showFloat f)
  | TkEncoded _ _ => str "# pre-encoded CBOR term"
  | TkEnd => str "# End of input"

partial def ppMapPairs : PP Unit := do
  nl; inc 3; indent; str " # key"; pprint; dec 3
  nl; inc 3; indent; str " # value"; pprint; dec 3

/-- Run `pp` for each item until the break, which is printed one level out. -/
partial def indef (pp : PP Unit) : PP Unit := do
  match ← peekTerm with
  | TkBreak TkEnd => dec 3; pprint
  | _ => pp; indef pp

end

/-- Pretty print an `Encoding` as annotated hex. -/
def prettyHexEnc (e : Encoding) : String :=
  match pprint.run ⟨e.toTokens, 0, ""⟩ with
  | .error s => s
  | .ok ((), { toks := TkEnd, out, .. }) => out
  | .ok ((), { out, .. }) =>
    out ++ "\nprettyEnc: Not all input was consumed (this is probably a problem with the pretty printing code)."

end Cborg.Pretty
