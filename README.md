# cborg

*CBOR serialisation for Lean 4, ported from Haskell's cborg.*

## abstract

This is a Lean 4 port of the Haskell [cborg](https://hackage.haskell.org/package/cborg)
library by Duncan Coutts and Well-Typed ([source](https://github.com/well-typed/cborg)).
It keeps the original design, which carries over naturally to Lean. An `Encoding` is a
difference list of tokens that gets serialised in one pass. A `Decoder` is a
continuation-passing monad: it describes which token it wants next, and a separate
interpreter feeds it bytes. The interpreter can take the whole input at once or in
chunks as they arrive from a socket. Both directions cover all of RFC 8949: integers
up to 64 bits and bignums beyond them, half, single and double floats, byte and text
strings, arrays, maps, tags, simple values, and indefinite-length forms. Each
primitive decoder has a canonical variant that rejects any non-minimal encoding.

The library depends on nothing but Lean core. It was written as the CBOR layer for a
Lean implementation of the [Katzenpost thin client](https://github.com/katzenpost/thin_client)
protocol.

## modules

| Lean module | Haskell module | contents |
|---|---|---|
| `Cborg.Encoding` | `Codec.CBOR.Encoding` | `Tokens`, `Encoding`, `encode*` |
| `Cborg.Write` | `Codec.CBOR.Write` | `toByteArray` |
| `Cborg.Decoding` | `Codec.CBOR.Decoding` | `DecodeAction`, `Decoder`, `decode*`, `decode*Canonical`, `peek*` |
| `Cborg.Read` | `Codec.CBOR.Read` | `deserialiseFromBytes`, `deserialiseIncremental`, `IDecode` |
| `Cborg.Term` | `Codec.CBOR.Term` | `Term`, `encodeTerm`, `decodeTerm` |
| `Cborg.FlatTerm` | `Codec.CBOR.FlatTerm` | `TermToken`, `toFlatTerm`, `fromFlatTerm`, `validFlatTerm` |
| `Cborg.Pretty` | `Codec.CBOR.Pretty` | `prettyHexEnc` annotated hex dumps |
| `Cborg.Magic` | `Codec.CBOR.Magic` | big-endian reads, half floats, bignum bytes |
| `Cborg.Diagnostic` | (from the test suite) | RFC 8949 diagnostic notation for `Term` |
| `Cborg.Serialise` | `Codec.Serialise.Class` (from `serialise`) | the `Serialise` class and record-map helpers |

Machine types map to Lean ones: `Word` becomes `UInt64`, `Int` becomes `Int64`,
`Integer` becomes `Int`, `Float` becomes `Float32`, `Double` becomes `Float`,
`ByteString` becomes `ByteArray`, and `Text` becomes `String`. List and map
lengths are `Nat`. Haskell's separate 32-bit-platform constructors and its
unpinned `ByteArray` variants are left out. `TBytesI` and `TStringI` keep their
chunks where Haskell uses lazy strings.

## usage

```lean
import Cborg
open Cborg

def frame : ByteArray :=
  toByteArray (encodeMapLen 2 ++ encodeString "epoch" ++ encodeWord64 42
                              ++ encodeString "id" ++ encodeBytes (ByteArray.mk #[1, 2, 3]))

def decodeFrame : Decoder (UInt64 × ByteArray) := do
  let n ← decodeMapLen
  if n != 2 then Decoder.fail "expected two fields"
  let _ ← decodeString; let epoch ← decodeWord64
  let _ ← decodeString; let id ← decodeBytes
  pure (epoch, id)

#eval deserialiseFromBytes decodeFrame frame |>.map (·.2.1)   -- Except.ok 42
```

To decode data of unknown shape, use `decodeTerm` and inspect the resulting `Term`.

## building and testing

```
lake build
make test
```

`make test` builds every test executable and runs it from the repository root, since the
test vectors are loaded from `testdata/` by relative path.

## license

This port is free software under the GNU General Public License, version 3 or (at
your option) any later version; see `LICENSE`.

It is a derivative work of Haskell cborg. Haskell cborg is Copyright (c) 2015-2017
Duncan Coutts, 2015-2017 Well-Typed LLP and 2015 IRIS Connect Ltd, and is
distributed under the BSD 3-Clause license. That license requires its copyright
notice, conditions and disclaimer to stay with redistributions, so they are kept
in `LICENSE.cborg`. Every ported source file says which Haskell module it comes
from. The RFC 7049 test vectors in `testdata/` come from the same project.
