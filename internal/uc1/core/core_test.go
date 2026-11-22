package core

import (
	"math/rand/v2"
	"reflect"
	"testing"
)

const (
	nSeq   = 1000
	maxLen = 200
)

// randEvent draws any event; o may be out of range, a may be 0.
func randEvent(r *rand.Rand, n uint32) Event {
	return Event{
		Kind: Kind(r.IntN(int(Restart) + 1)),
		O:    uint32(r.IntN(int(n) + 2)),
		A:    []uint32{0, 1, 5, 7}[r.IntN(4)],
		D:    Decision(r.IntN(2)),
		Svc:  Service(r.IntN(2)),
	}
}

// cover counts how often each antecedent of the property tests fired.
type cover struct {
	paid, failed, refunded, charge, refund, wireRefund, onTerminal, replay int
}

func (c *cover) observe(s State, e Event, s2 State, fx []Effect) {
	for o := range s2.Slots {
		switch s2.Slots[o].Ord.Status {
		case Paid:
			c.paid++
		case Failed:
			c.failed++
		case Refunded:
			c.refunded++
		}
	}
	for _, f := range fx {
		switch f.Kind {
		case Charge:
			c.charge++
		case Refund:
			c.refund++
		case WireRefundReq:
			c.wireRefund++
		}
	}
	orderEv := e.Kind <= RefundOrder
	if orderEv && s.OrderUp && IsTerminal(St(s, e.O)) && uint64(e.O) < uint64(len(s.Slots)) {
		c.onTerminal++
	}
	if e.Kind == ChargeReqRecv && s.ProvUp && e.A > 0 && Pr(s, e.O).Rec != NoRec && uint64(e.O) < uint64(len(s.Slots)) {
		c.replay++
	}
}

func (c *cover) require(t *testing.T) {
	t.Helper()
	t.Logf("coverage: paid=%d failed=%d refunded=%d charge=%d refund=%d wireRefund=%d onTerminal=%d replay=%d",
		c.paid, c.failed, c.refunded, c.charge, c.refund, c.wireRefund, c.onTerminal, c.replay)
	for name, n := range map[string]int{"paid": c.paid, "failed": c.failed, "refunded": c.refunded,
		"charge": c.charge, "refund": c.refund, "wireRefund": c.wireRefund,
		"onTerminal": c.onTerminal, "replay": c.replay} {
		if n == 0 {
			t.Fatalf("vacuous: antecedent %q never fired", name)
		}
	}
}

// forRuns calls f for every step of the seeded random runs and checks coverage.
func forRuns(t *testing.T, seed uint64, f func(s State, e Event, s2 State, fx []Effect)) {
	t.Helper()
	var c cover
	r := rand.New(rand.NewPCG(seed, seed^0x9e3779b97f4a7c15))
	for i := 0; i < nSeq; i++ {
		n := uint32(2 + r.IntN(2))
		s := Init(n)
		for j, l := 0, r.IntN(maxLen+1); j < l; j++ {
			e := randEvent(r, n)
			s2, fx := Step(s, e)
			c.observe(s, e, s2, fx)
			f(s, e, s2, fx)
			s = s2
		}
	}
	c.require(t)
}

func TestInv(t *testing.T) {
	if !Inv(Init(3)) || !Inv(Init(0)) {
		t.Fatal("Init must satisfy Inv")
	}
	bad := []func(*Slot){
		func(x *Slot) { x.Prov.ChargeCount = 1 },
		func(x *Slot) { x.Prov.Rec, x.Prov.ChargeCount = Approved, 2 },
		func(x *Slot) { x.Prov.Rec = Approved },
		func(x *Slot) { x.Prov.Rec, x.Prov.ChargeCount, x.Prov.RefundCount = Approved, 1, 2 },
		func(x *Slot) { x.Prov.Rec, x.Prov.ChargeCount = Declined, 1 },
		func(x *Slot) { x.Ord.OutRefund = true },
		func(x *Slot) { x.Ord.OutCharge = true },
	}
	for i, m := range bad {
		s := Init(2)
		m(&s.Slots[1])
		if Inv(s) {
			t.Errorf("bad case %d accepted", i)
		}
	}
	forRuns(t, 1, func(_ State, e Event, s2 State, _ []Effect) {
		if !Inv(s2) {
			t.Fatalf("Inv broken after %v: %+v", e, s2)
		}
	})
}

func TestP1NoDoubleCharge(t *testing.T) {
	var c cover
	r := rand.New(rand.NewPCG(2, 3))
	for i := 0; i < nSeq; i++ {
		n := uint32(2 + r.IntN(2))
		s := Init(n)
		charges := map[uint32]int{}
		for j, l := 0, r.IntN(maxLen+1); j < l; j++ {
			e := randEvent(r, n)
			s0 := s
			var fx []Effect
			s, fx = Step(s, e)
			c.observe(s0, e, s, fx)
			for _, f := range fx {
				if f.Kind == Charge {
					charges[f.O]++
				}
			}
			for o := uint32(0); o < n+2; o++ {
				if Pr(s, o).ChargeCount > 1 || charges[o] > 1 {
					t.Fatalf("seq %d step %d: order %d chargeCount=%d Charge effects=%d",
						i, j, o, Pr(s, o).ChargeCount, charges[o])
				}
			}
		}
	}
	c.require(t)
}

func TestP2aRefundNeverExceedsCharge(t *testing.T) {
	forRuns(t, 4, func(_ State, e Event, s2 State, _ []Effect) {
		for o := uint32(0); o < uint32(len(s2.Slots))+2; o++ {
			if p := Pr(s2, o); p.RefundCount > p.ChargeCount {
				t.Fatalf("after %v: order %d refund %d > charge %d", e, o, p.RefundCount, p.ChargeCount)
			}
		}
	})
}

func hasEffect(fx []Effect, k EffectKind, o uint32) bool {
	for _, f := range fx {
		if f.Kind == k && f.O == o {
			return true
		}
	}
	return false
}

func TestP2bRefundOnlyFromPaid(t *testing.T) {
	forRuns(t, 5, func(s State, e Event, s2 State, fx []Effect) {
		for o := uint32(0); o < uint32(len(s.Slots))+2; o++ {
			if St(s, o) != Refunded && St(s2, o) == Refunded && St(s, o) != Paid {
				t.Fatalf("(a) %v order %d", e, o)
			}
			if !Od(s, o).OutRefund && Od(s2, o).OutRefund && St(s, o) != Paid {
				t.Fatalf("(b) %v order %d", e, o)
			}
			if hasEffect(fx, WireRefundReq, o) && St(s, o) != Refunded {
				t.Fatalf("(c) %v order %d", e, o)
			}
			if hasEffect(fx, Refund, o) && Pr(s, o).Rec != Approved {
				t.Fatalf("(d) %v order %d", e, o)
			}
		}
	})
}

func TestP3TerminalStable(t *testing.T) {
	forRuns(t, 6, func(s State, e Event, s2 State, _ []Effect) {
		for o := uint32(0); o < uint32(len(s.Slots))+2; o++ {
			if IsTerminal(St(s, o)) &&
				(St(s2, o) != St(s, o) || Od(s2, o).Amount != Od(s, o).Amount) {
				t.Fatalf("%v changed terminal order %d: %+v -> %+v", e, o, Od(s, o), Od(s2, o))
			}
		}
	})
}

// --- pins ---

// base returns a 3-slot state with distinctive content in every slot so
// frame errors show. Slot 1 is the slot under test, set by f.
func base(f func(*Slot)) State {
	s := Init(3)
	s.Slots[0] = Slot{OrdRec{Paid, 9, true, false}, ProvRec{Approved, 1, 0, 9, true}}
	s.Slots[2] = Slot{OrdRec{Refunded, 4, false, true}, ProvRec{Declined, 0, 0, 0, false}}
	if f != nil {
		f(&s.Slots[1])
	}
	return s
}

func copyState(s State) State {
	s.Slots = append([]Slot(nil), s.Slots...)
	return s
}

// pin checks Step(s,e) == (mod(s), fx), that s is not mutated, and rule D
// for the receiving service (up = false) and an out-of-range order.
func pin(t *testing.T, s State, e Event, mod func(*Slot), fx []Effect) {
	t.Helper()
	before := copyState(s)
	want := copyState(s)
	if mod != nil {
		mod(&want.Slots[e.O])
	}
	got, gfx := Step(s, e)
	if !reflect.DeepEqual(s, before) {
		t.Fatalf("Step mutated input")
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("%v: state\n got %+v\nwant %+v", e, got, want)
	}
	if len(gfx) != len(fx) || (len(fx) > 0 && !reflect.DeepEqual(gfx, fx)) {
		t.Fatalf("%v: effects got %v want %v", e, gfx, fx)
	}
	ruleD(t, s, e)
}

func ruleD(t *testing.T, s State, e Event) {
	t.Helper()
	down := copyState(s)
	switch e.Kind {
	case PlaceOrder, RetryTimeout, FlushChargeReq, FlushRefundReq, PaymentApproved, PaymentDeclined, RefundOrder:
		down.OrderUp = false
	default:
		down.ProvUp = false
	}
	out := e
	out.O = uint32(len(s.Slots)) + uint32(len(s.Slots)%2)
	for _, c := range []struct {
		s State
		e Event
	}{{down, e}, {s, out}, {s, Event{Kind: e.Kind, O: ^uint32(0), A: e.A, D: e.D}}} {
		want := copyState(c.s)
		got, fx := Step(c.s, c.e)
		if !reflect.DeepEqual(got, want) || len(fx) != 0 {
			t.Fatalf("rule D violated for %+v: %+v %v", c.e, got, fx)
		}
	}
}

func TestPinPlaceOrder(t *testing.T) {
	e := Event{Kind: PlaceOrder, O: 1, A: 5}
	pin(t, base(nil), e, func(x *Slot) {
		x.Ord = OrdRec{AwaitingPayment, 5, true, false}
	}, nil)
	for _, st := range []Status{AwaitingPayment, Paid, Failed, Refunded} {
		pin(t, base(func(x *Slot) { x.Ord.Status, x.Ord.Amount = st, 3 }), e, nil, nil)
	}
	pin(t, base(nil), Event{Kind: PlaceOrder, O: 1, A: 0}, nil, nil)
}

func TestPinRetryTimeout(t *testing.T) {
	e := Event{Kind: RetryTimeout, O: 1}
	pin(t, base(func(x *Slot) { x.Ord = OrdRec{AwaitingPayment, 5, false, false} }), e,
		func(x *Slot) { x.Ord.OutCharge = true }, nil)
	for _, st := range []Status{None, Paid, Failed, Refunded} {
		pin(t, base(func(x *Slot) { x.Ord.Status = st }), e, nil, nil)
	}
}

func TestPinFlushChargeReq(t *testing.T) {
	e := Event{Kind: FlushChargeReq, O: 1}
	pin(t, base(func(x *Slot) { x.Ord = OrdRec{AwaitingPayment, 5, true, false} }), e,
		func(x *Slot) { x.Ord.OutCharge = false }, []Effect{{WireChargeReq, 1, 5}})
	pin(t, base(func(x *Slot) { x.Ord = OrdRec{Paid, 5, true, false} }), e,
		func(x *Slot) { x.Ord.OutCharge = false }, []Effect{{WireChargeReq, 1, 5}})
	pin(t, base(func(x *Slot) { x.Ord = OrdRec{AwaitingPayment, 5, false, false} }), e, nil, nil)
}

func TestPinPaymentApproved(t *testing.T) {
	e := Event{Kind: PaymentApproved, O: 1}
	pin(t, base(func(x *Slot) { x.Ord = OrdRec{AwaitingPayment, 5, true, false} }), e,
		func(x *Slot) { x.Ord.Status = Paid }, nil)
	for _, st := range []Status{None, Paid, Failed, Refunded} {
		pin(t, base(func(x *Slot) { x.Ord.Status = st }), e, nil, nil)
	}
}

func TestPinPaymentDeclined(t *testing.T) {
	e := Event{Kind: PaymentDeclined, O: 1}
	pin(t, base(func(x *Slot) { x.Ord = OrdRec{AwaitingPayment, 5, true, false} }), e,
		func(x *Slot) { x.Ord.Status = Failed }, nil)
	for _, st := range []Status{None, Paid, Failed, Refunded} {
		pin(t, base(func(x *Slot) { x.Ord.Status = st }), e, nil, nil)
	}
}

func TestPinRefundOrder(t *testing.T) {
	e := Event{Kind: RefundOrder, O: 1}
	pin(t, base(func(x *Slot) { x.Ord = OrdRec{Paid, 5, true, false} }), e,
		func(x *Slot) { x.Ord.Status, x.Ord.OutRefund = Refunded, true }, nil)
	for _, st := range []Status{None, AwaitingPayment, Failed, Refunded} {
		pin(t, base(func(x *Slot) { x.Ord.Status = st }), e, nil, nil)
	}
}

func TestPinFlushRefundReq(t *testing.T) {
	e := Event{Kind: FlushRefundReq, O: 1}
	pin(t, base(func(x *Slot) { x.Ord = OrdRec{Refunded, 5, false, true} }), e,
		func(x *Slot) { x.Ord.OutRefund = false }, []Effect{{WireRefundReq, 1, 0}})
	pin(t, base(func(x *Slot) { x.Ord = OrdRec{Refunded, 5, false, false} }), e, nil, nil)
}

func TestPinChargeReqRecv(t *testing.T) {
	ap := Event{Kind: ChargeReqRecv, O: 1, A: 5, D: Approve}
	de := Event{Kind: ChargeReqRecv, O: 1, A: 5, D: Decline}
	pin(t, base(nil), ap, func(x *Slot) {
		x.Prov = ProvRec{Approved, 1, 0, 5, true}
	}, []Effect{{Charge, 1, 5}})
	pin(t, base(nil), de, func(x *Slot) {
		x.Prov = ProvRec{Declined, 0, 0, 0, true}
	}, nil)
	// rec != NoRec: only outReply, whatever d and a say.
	for _, rec := range []Res{Approved, Declined} {
		for _, e := range []Event{ap, de, {Kind: ChargeReqRecv, O: 1, A: 8, D: Approve}} {
			cc := uint32(0)
			if rec == Approved {
				cc = 1
			}
			pre := func(x *Slot) { x.Prov = ProvRec{rec, cc, 0, 5, false} }
			pin(t, base(pre), e, func(x *Slot) { x.Prov.OutReply = true }, nil)
		}
	}
	// a = 0: F, also with a stored Declined and with NoRec + Decline.
	pin(t, base(func(x *Slot) { x.Prov.Rec = Declined }), Event{Kind: ChargeReqRecv, O: 1, A: 0, D: Approve}, nil, nil)
	pin(t, base(nil), Event{Kind: ChargeReqRecv, O: 1, A: 0, D: Decline}, nil, nil)
	// a = 0: F.
	pin(t, base(nil), Event{Kind: ChargeReqRecv, O: 1, A: 0, D: Approve}, nil, nil)
	pin(t, base(func(x *Slot) { x.Prov.Rec, x.Prov.ChargeCount = Approved, 1 }),
		Event{Kind: ChargeReqRecv, O: 1, A: 0}, nil, nil)
}

func TestPinFlushReply(t *testing.T) {
	e := Event{Kind: FlushReply, O: 1}
	pin(t, base(func(x *Slot) { x.Prov = ProvRec{Approved, 1, 0, 5, true} }), e,
		func(x *Slot) { x.Prov.OutReply = false }, []Effect{{WireApproved, 1, 0}})
	pin(t, base(func(x *Slot) { x.Prov = ProvRec{Declined, 0, 0, 0, true} }), e,
		func(x *Slot) { x.Prov.OutReply = false }, []Effect{{WireDeclined, 1, 0}})
	pin(t, base(func(x *Slot) { x.Prov = ProvRec{Approved, 1, 0, 5, false} }), e, nil, nil)
	pin(t, base(func(x *Slot) { x.Prov.OutReply = true }), e, nil, nil) // rec = NoRec
	pin(t, base(func(x *Slot) { x.Prov = ProvRec{Declined, 0, 0, 0, false} }), e, nil, nil)
}

func TestPinRefundReqRecv(t *testing.T) {
	e := Event{Kind: RefundReqRecv, O: 1}
	pin(t, base(func(x *Slot) { x.Prov = ProvRec{Approved, 1, 0, 5, false} }), e,
		func(x *Slot) { x.Prov.RefundCount = 1 }, []Effect{{Refund, 1, 5}})
	pin(t, base(func(x *Slot) { x.Prov = ProvRec{Approved, 1, 1, 5, false} }), e, nil, nil)
	pin(t, base(func(x *Slot) { x.Prov = ProvRec{Declined, 0, 0, 0, false} }), e, nil, nil)
	pin(t, base(nil), e, nil, nil)
}

func TestPinCrashRestart(t *testing.T) {
	for _, svc := range []Service{OrderSvc, Provider} {
		for _, k := range []Kind{Crash, Restart} {
			for _, o := range []uint32{0, 1, 99} { // rule D does not apply
				for _, up := range []bool{true, false} {
					s := base(nil)
					s.OrderUp, s.ProvUp = up, !up
					want := copyState(s)
					if svc == OrderSvc {
						want.OrderUp = k == Restart
					} else {
						want.ProvUp = k == Restart
					}
					got, fx := Step(s, Event{Kind: k, Svc: svc, O: o})
					if !reflect.DeepEqual(got, want) || len(fx) != 0 {
						t.Fatalf("%v %v: got %+v %v want %+v", k, svc, got, fx, want)
					}
				}
			}
		}
	}
}

func legal(a, b Status) bool {
	return a == b || (a == None && b == AwaitingPayment) || (a == AwaitingPayment && (b == Paid || b == Failed)) ||
		(a == Paid && b == Refunded)
}

func TestPinLegalTransitions(t *testing.T) {
	forRuns(t, 7, func(s State, e Event, s2 State, _ []Effect) {
		if len(s2.Slots) != len(s.Slots) {
			t.Fatalf("slot count changed by %v", e)
		}
		for o := uint32(0); o < uint32(len(s.Slots)); o++ {
			if !legal(St(s, o), St(s2, o)) {
				t.Fatalf("%v: %v -> %v", e, St(s, o), St(s2, o))
			}
		}
	})
}

func TestPinProvRecStable(t *testing.T) {
	forRuns(t, 8, func(s State, e Event, s2 State, _ []Effect) {
		for o := uint32(0); o < uint32(len(s.Slots)); o++ {
			a, b := Pr(s, o), Pr(s2, o)
			if a.Rec != b.Rec && !(a.Rec == NoRec && (b.Rec == Approved || b.Rec == Declined)) {
				t.Fatalf("%v: rec %v -> %v", e, a.Rec, b.Rec)
			}
			if b.ChargeCount < a.ChargeCount || b.RefundCount < a.RefundCount {
				t.Fatalf("%v: counts decreased", e)
			}
		}
	})
}

// Helper semantics.
func TestHelpersAbsentSlot(t *testing.T) {
	s := Init(2)
	if Get(s, 2) != (Slot{}) || Get(s, ^uint32(0)) != (Slot{}) || St(s, 5) != None {
		t.Fatal("absent slot must be the default slot")
	}
	if IsTerminal(Paid) || !IsTerminal(Failed) || !IsTerminal(Refunded) || IsTerminal(None) {
		t.Fatal("IsTerminal")
	}
}

// Rule D concerns only the receiving service: with the other service down
// the event takes effect exactly as with both up.
func TestRuleDOtherServiceDown(t *testing.T) {
	cases := []struct {
		e   Event
		pre func(*Slot)
	}{
		{Event{Kind: PlaceOrder, O: 1, A: 5}, nil},
		{Event{Kind: RetryTimeout, O: 1}, func(x *Slot) { x.Ord.Status, x.Ord.Amount = AwaitingPayment, 5 }},
		{Event{Kind: FlushChargeReq, O: 1}, func(x *Slot) { x.Ord = OrdRec{AwaitingPayment, 5, true, false} }},
		{Event{Kind: FlushRefundReq, O: 1}, func(x *Slot) { x.Ord = OrdRec{Refunded, 5, false, true} }},
		{Event{Kind: PaymentApproved, O: 1}, func(x *Slot) { x.Ord = OrdRec{AwaitingPayment, 5, false, false} }},
		{Event{Kind: PaymentDeclined, O: 1}, func(x *Slot) { x.Ord = OrdRec{AwaitingPayment, 5, false, false} }},
		{Event{Kind: RefundOrder, O: 1}, func(x *Slot) { x.Ord = OrdRec{Paid, 5, false, false} }},
		{Event{Kind: ChargeReqRecv, O: 1, A: 5, D: Approve}, nil},
		{Event{Kind: RefundReqRecv, O: 1}, func(x *Slot) { x.Prov = ProvRec{Approved, 1, 0, 5, false} }},
		{Event{Kind: FlushReply, O: 1}, func(x *Slot) { x.Prov = ProvRec{Approved, 1, 0, 5, true} }},
	}
	for _, c := range cases {
		s := base(c.pre)
		wantS, wantFx := Step(s, c.e)
		if reflect.DeepEqual(wantS, s) {
			t.Fatalf("%v: case has no effect, test is vacuous", c.e)
		}
		other := copyState(s)
		if c.e.Kind <= RefundOrder {
			other.ProvUp = false
		} else {
			other.OrderUp = false
		}
		gotS, gotFx := Step(other, c.e)
		want := copyState(wantS)
		if c.e.Kind <= RefundOrder {
			want.ProvUp = false
		} else {
			want.OrderUp = false
		}
		if !reflect.DeepEqual(gotS, want) || !reflect.DeepEqual(gotFx, wantFx) {
			t.Fatalf("%v with other service down: got %+v %v, want %+v %v", c.e, gotS, gotFx, want, wantFx)
		}
	}
}
