// Package mutants holds the UC1 mutants of properties/UC1.md section 5, each
// one bug written as a variant of core.Step. Every mutant has the signature of
// core.Step, except M3, which needs a mutant-only field and event (see M3State).
// Each variant handles only the buggy case itself and delegates every other
// event to core.Step, so the diff to the real core is exactly the bug.
package mutants

import "github.com/derangga/learn-formal-verification/internal/uc1/core"

// ProvApplyCharge is the mutant-only event of M3. It is a Kind value outside
// the contract enum (one past core.Restart); only StepM3 understands it, and
// core.Step treats it as an unknown event (a no-op that returns a copy).
const ProvApplyCharge core.Kind = core.Restart + 1

func clone(s core.State) core.State {
	t := s
	t.Slots = append([]core.Slot(nil), s.Slots...)
	return t
}

func inRange(s core.State, o uint32) bool { return uint64(o) < uint64(len(s.Slots)) }

// StepM1 removes the idempotency check: ChargeReqRecv with d = Approve ignores
// rec, adds 1 to chargeCount and emits Charge every time.
func StepM1(s core.State, e core.Event) (core.State, []core.Effect) {
	if e.Kind == core.ChargeReqRecv && s.ProvUp && inRange(s, e.O) && e.A > 0 && e.D == core.Approve {
		t := clone(s)
		p := &t.Slots[e.O].Prov
		p.Rec, p.ChargeCount, p.Amt, p.OutReply = core.Approved, p.ChargeCount+1, e.A, true
		return t, []core.Effect{{Kind: core.Charge, O: e.O, A: e.A}}
	}
	return core.Step(s, e)
}

// StepM2a is a refund without a status check: RefundOrder sets Refunded and
// queues the refund row in any status.
func StepM2a(s core.State, e core.Event) (core.State, []core.Effect) {
	if e.Kind == core.RefundOrder && s.OrderUp && inRange(s, e.O) {
		t := clone(s)
		o := &t.Slots[e.O].Ord
		o.Status, o.OutRefund = core.Refunded, true
		return t, nil
	}
	return core.Step(s, e)
}

// StepM2b is the provider refund without the refundCount < chargeCount guard:
// RefundReqRecv with rec = Approved always adds a refund row.
func StepM2b(s core.State, e core.Event) (core.State, []core.Effect) {
	if e.Kind == core.RefundReqRecv && s.ProvUp && inRange(s, e.O) && s.Slots[e.O].Prov.Rec == core.Approved {
		t := clone(s)
		p := &t.Slots[e.O].Prov
		p.RefundCount++
		return t, []core.Effect{{Kind: core.Refund, O: e.O, A: p.Amt}}
	}
	return core.Step(s, e)
}

// M3State is core.State plus the mutant-only field pending of ProvRec, kept as
// a slice parallel to Slots (len(Pending) == len(Slots)). core.ProvRec cannot
// carry the field without editing the core.
type M3State struct {
	core.State
	Pending []uint32
}

// InitM3 builds the empty M3 state with n slots.
func InitM3(n uint32) M3State {
	return M3State{State: core.Init(n), Pending: make([]uint32, n)}
}

// StepM3 is the check-then-act race. ChargeReqRecv with rec = NoRec, d = Approve
// and a > 0 only adds 1 to pending (it also stores the amount in amt, because
// ProvApplyCharge(o) carries none and Charge needs one). ProvApplyCharge(o)
// with pending > 0 subtracts 1, adds 1 to chargeCount, sets rec = Approved and
// emits Charge. Two copies both check while rec = NoRec, so two applies give
// chargeCount = 2. Every other event is core.Step on the embedded state with
// pending carried unchanged. Rule D (provider down, o out of range) applies to
// the two events above as to every provider event.
func StepM3(m M3State, e core.Event) (M3State, []core.Effect) {
	pend := append([]uint32(nil), m.Pending...)
	switch {
	case e.Kind == core.ChargeReqRecv && m.ProvUp && inRange(m.State, e.O) && e.A > 0 &&
		e.D == core.Approve && m.Slots[e.O].Prov.Rec == core.NoRec:
		t := clone(m.State)
		t.Slots[e.O].Prov.Amt = e.A
		pend[e.O]++
		return M3State{t, pend}, nil
	case e.Kind == ProvApplyCharge:
		if m.ProvUp && inRange(m.State, e.O) && pend[e.O] > 0 {
			t := clone(m.State)
			p := &t.Slots[e.O].Prov
			pend[e.O]--
			p.ChargeCount++
			p.Rec = core.Approved
			return M3State{t, pend}, []core.Effect{{Kind: core.Charge, O: e.O, A: p.Amt}}
		}
		return M3State{clone(m.State), pend}, nil
	}
	t, fx := core.Step(m.State, e)
	return M3State{t, pend}, fx
}

// StepM3Contract is StepM3 seen through the contract alphabet only: pending is
// not observable in core.State, so it is dropped. It is stateless, so it fits
// the harness StepFn; it models M3 with no ProvApplyCharge ever sent.
func StepM3Contract(s core.State, e core.Event) (core.State, []core.Effect) {
	m, fx := StepM3(M3State{State: s, Pending: make([]uint32, len(s.Slots))}, e)
	return m.State, fx
}

// StepM4 lets a late PaymentApproved set Paid without the AwaitingPayment guard.
func StepM4(s core.State, e core.Event) (core.State, []core.Effect) {
	if e.Kind == core.PaymentApproved && s.OrderUp && inRange(s, e.O) {
		t := clone(s)
		t.Slots[e.O].Ord.Status = core.Paid
		return t, nil
	}
	return core.Step(s, e)
}

// StepM5 dedupes the provider only on Approved: a ChargeReqRecv that arrives
// after Declined is handled as if rec were NoRec, so d = Approve approves and
// charges. chargeCount stays at most 1, so P1 to P3 and Inv never fail.
func StepM5(s core.State, e core.Event) (core.State, []core.Effect) {
	if e.Kind == core.ChargeReqRecv && s.ProvUp && inRange(s, e.O) && e.A > 0 && e.D == core.Approve &&
		s.Slots[e.O].Prov.Rec == core.Declined {
		t := clone(s)
		p := &t.Slots[e.O].Prov
		p.Rec, p.ChargeCount, p.Amt, p.OutReply = core.Approved, p.ChargeCount+1, e.A, true
		return t, []core.Effect{{Kind: core.Charge, O: e.O, A: e.A}}
	}
	return core.Step(s, e)
}
