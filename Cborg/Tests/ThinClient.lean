-- SPDX-License-Identifier: GPL-3.0-or-later

import Cborg.Tests.Util

/-!
# Katzenpost thin client messages

A few thin client messages written with `Serialise` and the record helpers, as
the Lean thin client will write them. The test decodes responses and requests
that the Go daemon's own types encoded (`testdata/thinclient`, made by
`scripts/gen-vectors`), and writes this side's encodings of the requests to
`.lake/thinclient` so `scripts/gen-vectors verify` can check them in Go.

Requests go out as one-entry maps, as the Rust and Python thin clients send
them; Go writes every variant key, all but one `null`, and both forms decode.
-/

namespace Cborg.Tests.ThinClient

abbrev Id16 := FixedBytes 16
abbrev Hash32 := FixedBytes 32

instance {n : Nat} : BEq (FixedBytes n) := ⟨fun a b => a.bytes.data == b.bytes.data⟩
instance {n : Nat} : Repr (FixedBytes n) := ⟨fun b _ => hex b.bytes⟩

def seq (start : UInt8) (n : Nat) : ByteArray := ⟨(Array.range n).map fun i => start + i.toUInt8⟩

def id16 (start : UInt8) : Id16 := ⟨seq start 16, by simp [seq, ByteArray.size]⟩
def hash32 (start : UInt8) : Hash32 := ⟨seq start 32, by simp [seq, ByteArray.size]⟩

instance : Repr ByteArray := ⟨fun b _ => hex b⟩

structure SessionTokenReply where
  appId : ByteArray
  resumed : Bool
  deriving BEq, Repr

instance : Serialise SessionTokenReply where
  encode r := encodeRecord [field "app_id" r.appId, field "resumed" r.resumed]
  decode := do
    let r ← decodeRecord
    return { appId := ← r.required "app_id", resumed := ← r.required "resumed" }

structure SphinxGeometry where
  packetLength : Nat
  nrHops : Nat
  userForwardPayloadLength : Nat
  nikeName : String
  kemName : String
  deriving BEq, Repr

def sphinxGeometryKeys : List String :=
  ["PacketLength", "NrHops", "HeaderLength", "RoutingInfoLength", "PerHopRoutingInfoLength",
   "SURBLength", "SphinxPlaintextHeaderLength", "PayloadTagLength", "ForwardPayloadLength",
   "UserForwardPayloadLength", "NextNodeHopLength", "SPRPKeyMaterialLength", "NIKEName", "KEMName"]

/-- Rust's `deny_unknown_fields`: keys outside the geometry's own are an error. -/
instance : Serialise SphinxGeometry where
  encode g := encodeRecord [field "PacketLength" g.packetLength, field "NrHops" g.nrHops,
    field "UserForwardPayloadLength" g.userForwardPayloadLength, field "NIKEName" g.nikeName,
    field "KEMName" g.kemName]
  decode := do
    let r ← decodeRecord
    r.onlyKeys sphinxGeometryKeys
    return {
      packetLength := ← r.required "PacketLength"
      nrHops := ← r.required "NrHops"
      userForwardPayloadLength := ← r.required "UserForwardPayloadLength"
      nikeName := ← r.required "NIKEName"
      kemName := ← r.withDefault "KEMName" "" }

structure ConnectionStatusEvent where
  isConnected : Bool
  err : Option String
  instanceToken : Id16
  sphinxGeometry : Option SphinxGeometry
  pigeonholeMaxPayload : Option Nat
  deriving BEq, Repr

instance : Serialise ConnectionStatusEvent where
  encode e := encodeRecord [field "is_connected" e.isConnected, nullableField "err" e.err,
    field "instance_token" e.instanceToken, optField "sphinx_geometry" e.sphinxGeometry,
    ("pigeonhole_geometry", e.pigeonholeMaxPayload.map fun n =>
      encodeRecord [field "MaxPlaintextPayloadLength" n])]
  decode := do
    let r ← decodeRecord
    let pigeonhole ← r.optional (α := Record) "pigeonhole_geometry"
    return {
      isConnected := ← r.required "is_connected"
      err := ← r.optional "err"
      instanceToken := ← r.required "instance_token"
      sphinxGeometry := ← r.optional "sphinx_geometry"
      pigeonholeMaxPayload := ← match pigeonhole with
        | some g => g.optional "MaxPlaintextPayloadLength"
        | none => pure none }

structure MessageReplyEvent where
  messageId : Option Id16
  surbId : Option Id16
  payload : ByteArray
  replyIndex : Option UInt8
  errorCode : UInt8
  deriving BEq, Repr

instance : Serialise MessageReplyEvent where
  encode e := encodeRecord [nullableField "message_id" e.messageId, nullableField "surbid" e.surbId,
    field "payload" e.payload, optField "reply_index" e.replyIndex, field "error_code" e.errorCode]
  decode := do
    let r ← decodeRecord
    return {
      messageId := ← r.optional "message_id"
      surbId := ← r.optional "surbid"
      payload := ← r.withDefault "payload" .empty
      replyIndex := ← r.optional "reply_index"
      errorCode := ← r.withDefault "error_code" 0 }

structure MessageSentEvent where
  messageId : Option Id16
  surbId : Option Id16
  sentAt : Int
  replyEta : Int
  forwardRoute : Array String
  deriving BEq, Repr

instance : Serialise MessageSentEvent where
  encode e := encodeRecord [nullableField "message_id" e.messageId, nullableField "surbid" e.surbId,
    field "sent_at" e.sentAt, field "reply_eta" e.replyEta, field "forward_route" e.forwardRoute]
  decode := do
    let r ← decodeRecord
    return {
      messageId := ← r.optional "message_id"
      surbId := ← r.optional "surbid"
      sentAt := ← r.required "sent_at"
      replyEta := ← r.required "reply_eta"
      forwardRoute := ← r.withDefault "forward_route" #[] }

/-- The PKI document travels as CBOR inside a byte string. -/
structure PKIDocument where
  epoch : UInt64
  serviceNodes : Array ByteArray
  topology : Array (Array String)
  deriving BEq, Repr

instance : Serialise PKIDocument where
  encode d := encodeRecord [field "Epoch" d.epoch, field "ServiceNodes" d.serviceNodes,
    field "Topology" d.topology]
  decode := do
    let r ← decodeRecord
    return {
      epoch := ← r.required "Epoch"
      serviceNodes := ← r.required "ServiceNodes"
      topology := ← r.required "Topology" }

structure GetPKIDocumentReply where
  queryId : Option Id16
  payload : ByteArray
  epoch : UInt64
  errorCode : UInt8
  deriving BEq, Repr

instance : Serialise GetPKIDocumentReply where
  encode e := encodeRecord [nullableField "query_id" e.queryId, field "payload" e.payload,
    field "epoch" e.epoch, field "error_code" e.errorCode]
  decode := do
    let r ← decodeRecord
    return {
      queryId := ← r.optional "query_id"
      payload := ← r.withDefault "payload" .empty
      epoch := ← r.required "epoch"
      errorCode := ← r.withDefault "error_code" 0 }

inductive Response where
  | sessionTokenReply (r : SessionTokenReply)
  | shutdownEvent
  | connectionStatusEvent (e : ConnectionStatusEvent)
  | messageReplyEvent (e : MessageReplyEvent)
  | messageSentEvent (e : MessageSentEvent)
  | newPKIDocumentEvent (payload : ByteArray)
  | getPKIDocumentReply (r : GetPKIDocumentReply)
  deriving BEq, Repr

/-- The one variant key whose value is not `null`, whatever else the map holds. -/
def _root_.Cborg.Record.variant (r : Record) : Decoder (String × ByteArray) :=
  match r.fields.filter (fun (_, v) => v.data != #[0xf6]) with
  | #[kv] => pure kv
  | kvs => Decoder.fail s!"expected one message, got {kvs.size}"

def sub {α : Type} [Serialise α] (raw : ByteArray) : Decoder α :=
  Decoder.ofExcept ((deserialise raw).mapError (·.msg))

instance : Serialise Response where
  encode
    | .sessionTokenReply r => encodeRecord [field "session_token_reply" r]
    | .shutdownEvent => encodeRecord [("shutdown_event", some (encodeMapLen 0))]
    | .connectionStatusEvent e => encodeRecord [field "connection_status_event" e]
    | .messageReplyEvent e => encodeRecord [field "message_reply_event" e]
    | .messageSentEvent e => encodeRecord [field "message_sent_event" e]
    | .newPKIDocumentEvent p =>
      encodeRecord [("new_pki_document_event", some (encodeRecord [field "payload" p]))]
    | .getPKIDocumentReply r => encodeRecord [field "get_pki_document_reply" r]
  decode := do
    let (key, raw) ← (← decodeRecord).variant
    match key with
    | "session_token_reply" => .sessionTokenReply <$> sub raw
    | "shutdown_event" => pure .shutdownEvent
    | "connection_status_event" => .connectionStatusEvent <$> sub raw
    | "message_reply_event" => .messageReplyEvent <$> sub raw
    | "message_sent_event" => .messageSentEvent <$> sub raw
    | "new_pki_document_event" => do
      let r : Record ← sub raw
      .newPKIDocumentEvent <$> r.required "payload"
    | "get_pki_document_reply" => .getPKIDocumentReply <$> sub raw
    | k => Decoder.fail s!"unknown response {k.quote}"

structure SendMessage where
  id : Option Id16
  withSurb : Bool
  surbId : Option Id16
  destinationIdHash : Option Hash32
  recipientQueueId : ByteArray
  payload : ByteArray
  deriving BEq, Repr

instance : Serialise SendMessage where
  encode m := encodeRecord [nullableField "id" m.id, field "with_surb" m.withSurb,
    nullableField "surbid" m.surbId, nullableField "destination_id_hash" m.destinationIdHash,
    field "recipient_queue_id" m.recipientQueueId, field "payload" m.payload]
  decode := do
    let r ← decodeRecord
    return {
      id := ← r.optional "id"
      withSurb := ← r.withDefault "with_surb" false
      surbId := ← r.optional "surbid"
      destinationIdHash := ← r.optional "destination_id_hash"
      recipientQueueId := ← r.withDefault "recipient_queue_id" .empty
      payload := ← r.withDefault "payload" .empty }

inductive Request where
  | sessionToken (clientInstanceToken : Id16)
  | thinClose
  | sendMessage (m : SendMessage)
  | getPKIDocument (queryId : Id16) (epoch : UInt64)
  deriving BEq, Repr

instance : Serialise Request where
  encode
    | .sessionToken t =>
      encodeRecord [("session_token", some (encodeRecord [field "client_instance_token" t]))]
    | .thinClose => encodeRecord [("thin_close", some (encodeMapLen 0))]
    | .sendMessage m => encodeRecord [field "send_message" m]
    | .getPKIDocument q e =>
      encodeRecord [("get_pki_document", some (encodeRecord [field "query_id" q, field "epoch" e]))]
  decode := do
    let (key, raw) ← (← decodeRecord).variant
    match key with
    | "session_token" => do
      let r : Record ← sub raw
      .sessionToken <$> r.required "client_instance_token"
    | "thin_close" => pure .thinClose
    | "send_message" => .sendMessage <$> sub raw
    | "get_pki_document" => do
      let r : Record ← sub raw
      return .getPKIDocument (← r.required "query_id") (← r.required "epoch")
    | k => Decoder.fail s!"unknown request {k.quote}"

def pkiDoc : PKIDocument :=
  { epoch := 123456, serviceNodes := #[seq 0xa0 4, seq 0xb0 4],
    topology := #[#["mix1", "mix2"], #["mix3"]] }

/-- The same values `scripts/gen-vectors` encodes. -/
def responses : List (String × Response) := [
  ("session_token_reply", .sessionTokenReply { appId := seq 0x40 16, resumed := true }),
  ("shutdown_event", .shutdownEvent),
  ("connection_status_event", .connectionStatusEvent {
    isConnected := true, err := none, instanceToken := id16 0x50,
    sphinxGeometry := some { packetLength := 3082, nrHops := 5, userForwardPayloadLength := 2000,
                             nikeName := "x25519", kemName := "" },
    pigeonholeMaxPayload := some 1553 }),
  ("message_reply_event", .messageReplyEvent {
    messageId := some (id16 0x60), surbId := none, payload := "hello mixnet".toUTF8,
    replyIndex := none, errorCode := 0 }),
  ("message_sent_event", .messageSentEvent {
    messageId := some (id16 0x70), surbId := some (id16 0x80), sentAt := 1700000000,
    replyEta := 1500000000, forwardRoute := #["gateway", "mix1", "service"] }),
  ("new_pki_document_event", .newPKIDocumentEvent (serialise pkiDoc)),
  ("get_pki_document_reply", .getPKIDocumentReply {
    queryId := some (id16 0x90), payload := serialise pkiDoc, epoch := 2 ^ 40 + 5,
    errorCode := 7 })]

def requests : List (String × Request) := [
  ("session_token", .sessionToken (id16 0x10)),
  ("thin_close", .thinClose),
  ("send_message", .sendMessage {
    id := some (id16 0x01), withSurb := true, surbId := some (id16 0x20),
    destinationIdHash := some (hash32 0x30), recipientQueueId := "courier".toUTF8,
    payload := seq 0 300 }),
  ("send_message_no_surb", .sendMessage {
    id := some (id16 0x02), withSurb := false, surbId := none,
    destinationIdHash := some (hash32 0x30), recipientQueueId := "courier".toUTF8,
    payload := .empty }),
  ("get_pki_document", .getPKIDocument (id16 0x90) (2 ^ 40 + 5))]

def checkDecodes {α : Type} [Serialise α] [BEq α] [Repr α] (name : String) (bs : ByteArray)
    (expected : α) : TestM Unit :=
  match deserialise (α := α) bs with
  | .ok a => check name (a == expected) fun _ => s!"got {repr a}"
  | .error e => check name false fun _ => toString e

def main : IO UInt32 := do
  let dir : System.FilePath := "testdata/thinclient"
  let out : System.FilePath := ".lake/thinclient"
  IO.FS.createDirAll out
  runSuite "ThinClient" do
    for (name, expected) in responses do
      let bs ← IO.FS.readBinFile (dir / s!"{name}.cbor")
      checkDecodes s!"Go {name}" bs expected
      checkDecodes s!"Lean {name}" (serialise expected) expected
    -- the PKI document inside the byte string decodes in its turn
    match deserialise (α := Response) (← IO.FS.readBinFile (dir / "new_pki_document_event.cbor")) with
    | .ok (.newPKIDocumentEvent payload) => checkDecodes "embedded PKI document" payload pkiDoc
    | _ => check "embedded PKI document" false
    for (name, expected) in requests do
      let bs ← IO.FS.readBinFile (dir / s!"{name}.cbor")
      checkDecodes s!"Go {name}" bs expected
      let mine := serialise expected
      checkDecodes s!"Lean {name}" mine expected
      IO.FS.writeBinFile (out / s!"{name}.cbor") mine
    -- one-entry maps, as Rust writes them
    checkEq "session_token bytes"
      "a16d73657373696f6e5f746f6b656ea175636c69656e745f696e7374616e63655f746f6b656e50101112131415161718191a1b1c1d1e1f"
      (hex (serialise (Request.sessionToken (id16 0x10))))
    -- a record field of the wrong type names the field
    match deserialise (α := SessionTokenReply) (unhex "a2666170705f6964f567726573756d6564f5") with
    | .error e => checkEq "field type error" "field \"app_id\": expected bytes" e.msg
    | .ok _ => check "field type error" false
    match deserialise (α := SessionTokenReply) (unhex "a267617070735f69644067726573756d6564f5") with
    | .error e => checkEq "missing field" "missing field \"app_id\"" e.msg
    | .ok _ => check "missing field" false
    match deserialise (α := SessionTokenReply) (unhex "a2666170705f696440666170705f696440") with
    | .error e => checkEq "duplicate key" "duplicate key \"app_id\"" e.msg
    | .ok _ => check "duplicate key" false

end Cborg.Tests.ThinClient

def main : IO UInt32 := Cborg.Tests.ThinClient.main
