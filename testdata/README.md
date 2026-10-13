# testdata

`appendix_a.json` holds every example from RFC 7049 Appendix A. It is copied from
Haskell cborg's `tests/test-vectors/appendix_a.json` (BSD-3-Clause, see
`LICENSE.cborg`), which takes it from https://github.com/cbor/test-vectors.

`thinclient/` holds Katzenpost thin client messages as the Go daemon encodes them,
made with its own message types and CBOR library by `scripts/gen-vectors`
(`make vectors`). The Go daemon writes every variant key of a response or request,
all `null` except one, so these maps are much larger than the one-entry maps the
Rust and Python thin clients send.
