// SPDX-License-Identifier: GPL-3.0-or-later

// gen-vectors writes thin client messages encoded by the Katzenpost Go daemon's
// own types and CBOR library, and checks that messages encoded by Lean cborg
// decode into the same Go values.
//
//	go run . gen ../../testdata/thinclient
//	go run . verify ../../.lake/thinclient
package main

import (
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"time"

	"github.com/fxamacker/cbor/v2"

	"github.com/katzenpost/katzenpost/client/thin"
	"github.com/katzenpost/katzenpost/core/sphinx/geo"
	pgeo "github.com/katzenpost/katzenpost/pigeonhole/geo"
)

// seq returns n bytes counting up from start.
func seq(start byte, n int) []byte {
	b := make([]byte, n)
	for i := range b {
		b[i] = start + byte(i)
	}
	return b
}

func id16(start byte) *[16]byte {
	var a [16]byte
	copy(a[:], seq(start, 16))
	return &a
}

func id32(start byte) *[32]byte {
	var a [32]byte
	copy(a[:], seq(start, 32))
	return &a
}

type vector struct {
	name string
	v    any
}

// pkiDoc stands in for a PKI document: a CBOR map carried inside a byte string.
type pkiDoc struct {
	Epoch        uint64
	ServiceNodes [][]byte
	Topology     [][]string
}

func responses() []vector {
	doc, err := cbor.Marshal(pkiDoc{
		Epoch:        123456,
		ServiceNodes: [][]byte{seq(0xa0, 4), seq(0xb0, 4)},
		Topology:     [][]string{{"mix1", "mix2"}, {"mix3"}},
	})
	if err != nil {
		panic(err)
	}
	return []vector{
		{"session_token_reply", &thin.Response{
			SessionTokenReply: &thin.SessionTokenReply{AppID: seq(0x40, 16), Resumed: true},
		}},
		{"shutdown_event", &thin.Response{ShutdownEvent: &thin.ShutdownEvent{}}},
		{"connection_status_event", &thin.Response{
			ConnectionStatusEvent: &thin.ConnectionStatusEvent{
				IsConnected:   true,
				InstanceToken: *id16(0x50),
				SphinxGeometry: &geo.Geometry{
					PacketLength: 3082, NrHops: 5, HeaderLength: 476, RoutingInfoLength: 410,
					PerHopRoutingInfoLength: 82, SURBLength: 572, SphinxPlaintextHeaderLength: 2,
					PayloadTagLength: 32, ForwardPayloadLength: 2574, UserForwardPayloadLength: 2000,
					NextNodeHopLength: 65, SPRPKeyMaterialLength: 64,
					NIKEName: "x25519", KEMName: "",
				},
				PigeonholeGeometry: &pgeo.Geometry{
					MaxPlaintextPayloadLength: 1553, CourierQueryReadLength: 290,
					CourierQueryWriteLength: 1838, CourierQueryReplyReadLength: 1700,
					CourierQueryReplyWriteLength: 110, NIKEName: "x25519",
					SignatureSchemeName: "Ed25519",
				},
			},
		}},
		{"message_reply_event", &thin.Response{
			MessageReplyEvent: &thin.MessageReplyEvent{
				MessageID: id16(0x60),
				Payload:   []byte("hello mixnet"),
				ErrorCode: 0,
			},
		}},
		{"message_sent_event", &thin.Response{
			MessageSentEvent: &thin.MessageSentEvent{
				MessageID:    id16(0x70),
				SURBID:       id16(0x80),
				SentAt:       time.Unix(1700000000, 0).UTC(),
				ReplyETA:     1500 * time.Millisecond,
				ForwardRoute: []string{"gateway", "mix1", "service"},
			},
		}},
		{"new_pki_document_event", &thin.Response{
			NewPKIDocumentEvent: &thin.NewPKIDocumentEvent{Payload: doc},
		}},
		{"get_pki_document_reply", &thin.Response{
			GetPKIDocumentReply: &thin.GetPKIDocumentReply{
				QueryID: id16(0x90), Payload: doc, Epoch: 1<<40 + 5, ErrorCode: 7,
			},
		}},
	}
}

func requests() []vector {
	return []vector{
		{"session_token", &thin.Request{
			SessionToken: &thin.SessionToken{ClientInstanceToken: *id16(0x10)},
		}},
		{"thin_close", &thin.Request{ThinClose: &thin.ThinClose{}}},
		{"send_message", &thin.Request{
			SendMessage: &thin.SendMessage{
				ID:                id16(0x01),
				WithSURB:          true,
				SURBID:            id16(0x20),
				DestinationIdHash: id32(0x30),
				RecipientQueueID:  []byte("courier"),
				Payload:           seq(0, 300),
			},
		}},
		{"send_message_no_surb", &thin.Request{
			SendMessage: &thin.SendMessage{
				ID:                id16(0x02),
				DestinationIdHash: id32(0x30),
				RecipientQueueID:  []byte("courier"),
				Payload:           []byte{},
			},
		}},
		{"get_pki_document", &thin.Request{
			GetPKIDocument: &thin.GetPKIDocument{QueryID: id16(0x90), Epoch: 1<<40 + 5},
		}},
	}
}

func gen(dir string) error {
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	for _, v := range append(responses(), requests()...) {
		blob, err := cbor.Marshal(v.v)
		if err != nil {
			return fmt.Errorf("%s: %w", v.name, err)
		}
		if err := os.WriteFile(filepath.Join(dir, v.name+".cbor"), blob, 0o644); err != nil {
			return err
		}
	}
	return nil
}

func verify(dir string) error {
	failed := 0
	for _, v := range requests() {
		blob, err := os.ReadFile(filepath.Join(dir, v.name+".cbor"))
		if err != nil {
			return err
		}
		got := new(thin.Request)
		if err := cbor.Unmarshal(blob, got); err != nil {
			fmt.Printf("FAIL %s: %v\n", v.name, err)
			failed++
			continue
		}
		if !reflect.DeepEqual(got, v.v) {
			fmt.Printf("FAIL %s: decoded %+v\n", v.name, got)
			failed++
			continue
		}
		fmt.Printf("ok   %s\n", v.name)
	}
	if failed > 0 {
		return fmt.Errorf("%d requests did not match", failed)
	}
	return nil
}

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: gen-vectors gen|verify DIR")
		os.Exit(2)
	}
	var err error
	switch os.Args[1] {
	case "gen":
		err = gen(os.Args[2])
	case "verify":
		err = verify(os.Args[2])
	default:
		err = fmt.Errorf("unknown command %q", os.Args[1])
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
