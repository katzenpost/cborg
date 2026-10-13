-- SPDX-License-Identifier: GPL-3.0-or-later

import Cborg.Tests.Util

/-!
# Corpus round trip

Decode every `.cbor` file in a directory with `decodeTerm`, re-encode it, and
check the bytes come back unchanged. `scripts/cbor2_check.py` fills the
directory with items Python's cbor2 encoded.

    Cborg-Tests-Corpus DIR
-/

namespace Cborg.Tests.Corpus

def main (args : List String) : IO UInt32 := do
  let [dir] := args | IO.eprintln "usage: Cborg-Tests-Corpus DIR"; return 2
  let files := (← System.FilePath.readDir dir).filter (·.path.extension == some "cbor")
  let files := files.qsort (·.fileName < ·.fileName)
  runSuite s!"Corpus {dir}" do
    for f in files do
      let bs ← IO.FS.readBinFile f.path
      match decodeAll decodeTerm bs with
      | .error e => check f.fileName false fun _ => s!"{e}: {hex bs}"
      | .ok t =>
        let again := toByteArray (encodeTerm t)
        check f.fileName (again == bs) fun _ => s!"{t}: re-encoded {hex again}, cbor2 wrote {hex bs}"

end Cborg.Tests.Corpus

def main (args : List String) : IO UInt32 := Cborg.Tests.Corpus.main args
