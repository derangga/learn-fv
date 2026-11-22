// Package core is the pure UC1 step function (properties/UC1.md sections 2 to 4).
// TLA+ and the Bend port mirror Step; nothing here does I/O.
package core

// Status is the order status. Values follow the contract order.
type Status uint8

const (
	None Status = iota
	AwaitingPayment
	Paid
	Failed
	Refunded
)

func (x Status) String() string {
	switch x {
	case None:
		return "None"
	case AwaitingPayment:
		return "AwaitingPayment"
	case Paid:
		return "Paid"
	case Failed:
		return "Failed"
	case Refunded:
		return "Refunded"
	}
	return "Status(?)"
}

// Res is the provider's idempotency record.
type Res uint8

const (
	NoRec Res = iota
	Approved
	Declined
)

func (x Res) String() string {
	switch x {
	case NoRec:
		return "NoRec"
	case Approved:
		return "Approved"
	case Declined:
		return "Declined"
	}
	return "Res(?)"
}

// Decision is the card issuer's answer, carried by ChargeReqRecv.
type Decision uint8

const (
	Approve Decision = iota
	Decline
)

func (x Decision) String() string {
	switch x {
	case Approve:
		return "Approve"
	case Decline:
		return "Decline"
	}
	return "Decision(?)"
}

// Service names a service for Crash and Restart.
type Service uint8

const (
	OrderSvc Service = iota
	Provider
)

func (x Service) String() string {
	switch x {
	case OrderSvc:
		return "OrderSvc"
	case Provider:
		return "Provider"
	}
	return "Service(?)"
}

// OrdRec is the order service side of a slot.
type OrdRec struct {
	Status    Status
	Amount    uint32
	OutCharge bool
	OutRefund bool
}

// ProvRec is the provider side of a slot.
type ProvRec struct {
	Rec         Res
	ChargeCount uint32
	RefundCount uint32
	Amt         uint32
	OutReply    bool
}

// Slot is the state of one order id.
type Slot struct {
	Ord  OrdRec
	Prov ProvRec
}

// State is the whole system state. Slots is a slice indexed by order id.
type State struct {
	Slots   []Slot
	OrderUp bool
	ProvUp  bool
}

// Kind is the event kind. Values follow the contract table order.
type Kind uint8

const (
	PlaceOrder Kind = iota
	RetryTimeout
	FlushChargeReq
	FlushRefundReq
	PaymentApproved
	PaymentDeclined
	RefundOrder
	ChargeReqRecv
	RefundReqRecv
	FlushReply
	Crash
	Restart
)

var kindNames = [...]string{
	"PlaceOrder", "RetryTimeout", "FlushChargeReq", "FlushRefundReq",
	"PaymentApproved", "PaymentDeclined", "RefundOrder", "ChargeReqRecv",
	"RefundReqRecv", "FlushReply", "Crash", "Restart",
}

func (k Kind) String() string {
	if int(k) < len(kindNames) {
		return kindNames[k]
	}
	return "Kind(?)"
}

// Event is one atomic input to Step. Unused fields are ignored.
type Event struct {
	Kind Kind
	O    uint32
	A    uint32
	D    Decision
	Svc  Service
}

// EffectKind is the effect kind. Values follow the contract order.
type EffectKind uint8

const (
	WireChargeReq EffectKind = iota
	WireRefundReq
	WireApproved
	WireDeclined
	Charge
	Refund
)

var effectNames = [...]string{
	"WireChargeReq", "WireRefundReq", "WireApproved", "WireDeclined", "Charge", "Refund",
}

func (k EffectKind) String() string {
	if int(k) < len(effectNames) {
		return effectNames[k]
	}
	return "EffectKind(?)"
}

// Effect is one output of Step. A is 0 where the contract gives no amount.
type Effect struct {
	Kind EffectKind
	O    uint32
	A    uint32
}

// Init builds the state with n empty slots, both services up.
func Init(n uint32) State {
	return State{Slots: make([]Slot, n), OrderUp: true, ProvUp: true}
}

// Get returns slot o, or the default slot when o is out of range.
func Get(s State, o uint32) Slot {
	if uint64(o) < uint64(len(s.Slots)) {
		return s.Slots[o]
	}
	return Slot{}
}

func St(s State, o uint32) Status  { return Get(s, o).Ord.Status }
func Pr(s State, o uint32) ProvRec { return Get(s, o).Prov }
func Od(s State, o uint32) OrdRec  { return Get(s, o).Ord }

// IsTerminal reports whether x is Failed or Refunded.
func IsTerminal(x Status) bool { return x == Failed || x == Refunded }

// Step applies one event. It is total, deterministic and never mutates s.
func Step(s State, e Event) (State, []Effect) {
	switch e.Kind {
	case Crash, Restart:
		t := s
		t.Slots = append([]Slot(nil), s.Slots...)
		up := e.Kind == Restart
		switch e.Svc {
		case OrderSvc:
			t.OrderUp = up
		case Provider:
			t.ProvUp = up
		}
		return t, nil
	case PlaceOrder, RetryTimeout, FlushChargeReq, FlushRefundReq,
		PaymentApproved, PaymentDeclined, RefundOrder:
		if !s.OrderUp {
			break
		}
		return stepOrder(s, e)
	case ChargeReqRecv, RefundReqRecv, FlushReply:
		if !s.ProvUp {
			break
		}
		return stepProv(s, e)
	}
	return clone(s), nil
}

func clone(s State) State {
	t := s
	t.Slots = append([]Slot(nil), s.Slots...)
	return t
}

// stepOrder handles order-service events; rule D already covers OrderUp.
func stepOrder(s State, e Event) (State, []Effect) {
	t := clone(s)
	if uint64(e.O) >= uint64(len(t.Slots)) {
		return t, nil
	}
	sl := &t.Slots[e.O]
	o := &sl.Ord
	var fx []Effect
	switch e.Kind {
	case PlaceOrder:
		if e.A > 0 && o.Status == None {
			o.Status, o.Amount, o.OutCharge = AwaitingPayment, e.A, true
		}
	case RetryTimeout:
		if o.Status == AwaitingPayment {
			o.OutCharge = true
		}
	case FlushChargeReq:
		if o.OutCharge {
			o.OutCharge = false
			fx = []Effect{{WireChargeReq, e.O, o.Amount}}
		}
	case PaymentApproved:
		if o.Status == AwaitingPayment {
			o.Status = Paid
		}
	case PaymentDeclined:
		if o.Status == AwaitingPayment {
			o.Status = Failed
		}
	case RefundOrder:
		if o.Status == Paid {
			o.Status, o.OutRefund = Refunded, true
		}
	case FlushRefundReq:
		if o.OutRefund {
			o.OutRefund = false
			fx = []Effect{{WireRefundReq, e.O, 0}}
		}
	}
	return t, fx
}

// stepProv handles provider events; rule D already covers ProvUp.
func stepProv(s State, e Event) (State, []Effect) {
	t := clone(s)
	if uint64(e.O) >= uint64(len(t.Slots)) {
		return t, nil
	}
	p := &t.Slots[e.O].Prov
	var fx []Effect
	switch e.Kind {
	case ChargeReqRecv:
		if e.A == 0 {
			break
		}
		switch {
		case p.Rec != NoRec:
			p.OutReply = true
		case e.D == Approve:
			p.Rec, p.ChargeCount, p.Amt, p.OutReply = Approved, p.ChargeCount+1, e.A, true
			fx = []Effect{{Charge, e.O, e.A}}
		case e.D == Decline:
			p.Rec, p.OutReply = Declined, true
		}
	case FlushReply:
		if p.OutReply && p.Rec != NoRec {
			p.OutReply = false
			if p.Rec == Approved {
				fx = []Effect{{WireApproved, e.O, 0}}
			} else {
				fx = []Effect{{WireDeclined, e.O, 0}}
			}
		}
	case RefundReqRecv:
		if p.Rec == Approved && p.RefundCount < p.ChargeCount {
			p.RefundCount++
			fx = []Effect{{Refund, e.O, p.Amt}}
		}
	}
	return t, fx
}

// Inv is the contract invariant (section 3).
func Inv(s State) bool {
	for o := range s.Slots {
		i := uint32(o)
		p, d := Pr(s, i), Od(s, i)
		want := uint32(0)
		if p.Rec == Approved {
			want = 1
		}
		if p.ChargeCount != want || p.RefundCount > p.ChargeCount {
			return false
		}
		if d.OutRefund && St(s, i) != Refunded {
			return false
		}
		if d.OutCharge && St(s, i) == None {
			return false
		}
	}
	return true
}
