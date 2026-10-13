# SPDX-License-Identifier: GPL-3.0-or-later
"""Cross-check Lean cborg against Python's cbor2, which the Python thin client uses.

Run from the repository root after `make test`, which writes Lean's thin client
requests to .lake/thinclient:

    python -I scripts/cbor2_check.py corpus DIR   # write cbor2-encoded items to DIR
    python -I scripts/cbor2_check.py check        # compare thin client messages

`make pycheck` does both and runs Lean over the corpus.
"""

import math
import pathlib
import random
import sys

import cbor2

THINCLIENT = pathlib.Path("testdata/thinclient")
LEAN_OUT = pathlib.Path(".lake/thinclient")


def seq(start, n):
    return bytes((start + i) % 256 for i in range(n))


# The requests the Lean test encodes, built the way katzenpost_thinclient/core.py builds them.
REQUESTS = {
    "session_token": {"session_token": {"client_instance_token": seq(0x10, 16)}},
    "thin_close": {"thin_close": {}},
    "send_message": {"send_message": {
        "id": seq(0x01, 16),
        "with_surb": True,
        "surbid": seq(0x20, 16),
        "destination_id_hash": seq(0x30, 32),
        "recipient_queue_id": b"courier",
        "payload": seq(0, 300),
    }},
    "send_message_no_surb": {"send_message": {
        "id": seq(0x02, 16),
        "with_surb": False,
        "surbid": None,
        "destination_id_hash": seq(0x30, 32),
        "recipient_queue_id": b"courier",
        "payload": b"",
    }},
    "get_pki_document": {"get_pki_document": {"query_id": seq(0x90, 16), "epoch": 2**40 + 5}},
}


def check():
    failed = 0

    def fail(msg):
        nonlocal failed
        failed += 1
        print("FAIL", msg)

    for name, value in REQUESTS.items():
        lean = (LEAN_OUT / f"{name}.cbor").read_bytes()
        mine = cbor2.dumps(value)
        if lean != mine:
            fail(f"{name}: Lean wrote {lean.hex()}, cbor2 writes {mine.hex()}")
        elif cbor2.loads(lean) != value:
            fail(f"{name}: cbor2 reads {cbor2.loads(lean)!r}")
        else:
            print(f"ok   {name}: Lean bytes equal cbor2's")

    # every Go-encoded message loads, with exactly one non-null variant
    for path in sorted(THINCLIENT.glob("*.cbor")):
        msg = cbor2.loads(path.read_bytes())
        present = [k for k, v in msg.items() if v is not None]
        if len(present) != 1 or not path.stem.startswith(present[0]):
            fail(f"{path.name}: variants {present}")
        else:
            print(f"ok   {path.name}: cbor2 loads the Go encoding")

    pki = cbor2.loads(THINCLIENT.joinpath("new_pki_document_event.cbor").read_bytes())
    doc = cbor2.loads(pki["new_pki_document_event"]["payload"])
    if doc != {"Epoch": 123456, "ServiceNodes": [seq(0xA0, 4), seq(0xB0, 4)],
               "Topology": [["mix1", "mix2"], ["mix3"]]}:
        fail(f"embedded PKI document: {doc!r}")

    print(f"cbor2 check: {failed} failed")
    return 1 if failed else 0


def random_value(rng, depth):
    kind = rng.randrange(14 if depth else 10)
    if kind == 0:
        return rng.randrange(-(2**64), 2**64)
    if kind == 1:
        return rng.choice([-1, 1]) * rng.randrange(2**64, 2**80)
    if kind == 2:
        return rng.choice([0, 23, 24, 255, 256, 65535, 65536, 2**32 - 1, 2**32, -24, -25])
    if kind == 3:
        return rng.choice([rng.uniform(-1e10, 1e10), 0.0, -0.0, 1.5, math.inf, -math.inf,
                           5.960464477539063e-08, 1e300, math.ldexp(1, -1074)])
    if kind == 4:
        return rng.randbytes(rng.randrange(40))
    if kind == 5:
        return "".join(chr(rng.choice([rng.randrange(0x20, 0x7F), rng.randrange(0x80, 0xD800),
                                       rng.randrange(0xE000, 0x110000)]))
                       for _ in range(rng.randrange(20)))
    if kind == 6:
        return rng.choice([True, False, None, cbor2.undefined])
    if kind == 7:
        return cbor2.CBORSimpleValue(rng.choice([0, 16, 19, 32, 255]))
    if kind == 8:
        return math.nan
    if kind == 9:
        return rng.randrange(2**63)
    if kind in (10, 11):
        return [random_value(rng, depth - 1) for _ in range(rng.randrange(6))]
    if kind == 12:
        return {rng.choice([str(i), i]): random_value(rng, depth - 1) for i in range(rng.randrange(6))}
    return cbor2.CBORTag(rng.choice([0, 1, 4, 24, 32, 100, 2**40]), random_value(rng, depth - 1))


def corpus(out, n=3000):
    out = pathlib.Path(out)
    out.mkdir(parents=True, exist_ok=True)
    for old in out.glob("*.cbor"):
        old.unlink()
    for i in range(n):
        rng = random.Random(i)
        value = random_value(rng, 4)
        # both the default and the canonical encoder, which narrows floats and sorts keys
        data = cbor2.dumps(value, canonical=bool(i % 2))
        (out / f"{i:05}.cbor").write_bytes(data)
    print(f"wrote {n} cbor2 items to {out}")
    return 0


if __name__ == "__main__":
    if sys.argv[1:2] == ["check"]:
        sys.exit(check())
    if sys.argv[1:2] == ["corpus"] and len(sys.argv) == 3:
        sys.exit(corpus(sys.argv[2]))
    print(__doc__)
    sys.exit(2)
