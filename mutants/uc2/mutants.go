// Package mutants holds the UC2 mutants of properties/UC2.md section 5, each
// one bug written as a variant of core.Step. Every mutant has the signature of
// core.Step, except M4, which needs a mutant-only state field and two
// mutant-only events (see M4State). Each variant handles only its buggy case
// and delegates every other event to core.Step, so the diff to the real core
// is exactly the bug. M5a has no Bend counterpart (Nat truncates).
package mutants

import "github.com/derangga/learn-formal-verification/internal/uc2/core"

// ReserveCheck and ReserveCommit are the mutant-only events of M4. They are
// Kind values outside the contract enum (one and two past core.Restart); only
// StepM4 understands them, and core.Step treats them as unknown events (a
// no-op that returns a copy). ReserveCheck uses ID, Sku, Qty, Ttl;
// ReserveCommit uses ID.
const (
	ReserveCheck  core.Kind = core.Restart + 1
	ReserveCommit core.Kind = core.Restart + 2
)

func clone(s core.State) core.State {
	s.Stocks = append([]core.Stock(nil), s.Stocks...)
	s.Res = append([]core.Res(nil), s.Res...)
	return s
}

func findStock(s core.State, sku int64) int {
	for i := range s.Stocks {
		if s.Stocks[i].Sku == sku {
			return i
		}
	}
	return -1
}

func findRes(s core.State, id int64) int {
	for i := range s.Res {
		if s.Res[i].ID == id {
			return i
		}
	}
	return -1
}

// recOf returns the index of record id when the service is up and the event
// is of kind k (else -1), so a mutant can test its own trigger in one line.
func recOf(s core.State, e core.Event, k core.Kind) int {
	if !s.Up || e.Kind != k {
		return -1
	}
	return findRes(s, e.ID)
}

// confirmApply is everything S4 does to record ri (a private copy of s).
func confirmApply(s core.State, ri int) (core.State, []core.Effect) {
	t := clone(s)
	r := &t.Res[ri]
	if ki := findStock(t, r.Sku); ki >= 0 {
		t.Stocks[ki].Reserved -= r.Qty
		t.Stocks[ki].Sold += r.Qty
	}
	r.Status = core.Confirmed
	r.ConfirmedAt = t.Clock
	return t, []core.Effect{{Kind: core.FxConfirmed, ID: r.ID}}
}

// expireApply is everything S6 does to record ri. leak = M6: reserved is not reduced.
func expireApply(s core.State, ri int, leak bool) (core.State, []core.Effect) {
	t := clone(s)
	r := &t.Res[ri]
	if ki := findStock(t, r.Sku); ki >= 0 {
		if !leak {
			t.Stocks[ki].Reserved -= r.Qty
		}
		t.Stocks[ki].Available += r.Qty
	}
	r.Status = core.Expired
	r.Returned++
	return t, []core.Effect{{Kind: core.FxReleased, ID: r.ID, Qty: r.Qty}}
}

// reserveApply is S2 with the stock's available counter set by take (so M5 can
// truncate and M5a can go negative). It does not check anything.
func reserveApply(s core.State, ki int, e core.Event, take func(avail, qty int64) int64) (core.State, []core.Effect) {
	t := clone(s)
	k := &t.Stocks[ki]
	exp := t.Clock + e.Ttl
	k.Available = take(k.Available, e.Qty)
	k.Reserved += e.Qty
	t.Res = append(t.Res, core.Res{ID: e.ID, Sku: e.Sku, Qty: e.Qty, Status: core.Held, ExpiresAt: exp})
	return t, []core.Effect{{Kind: core.FxReserved, ID: e.ID, Sku: e.Sku, Qty: e.Qty, ExpiresAt: exp}}
}

func plainSub(a, q int64) int64 { return a - q }

func truncSub(a, q int64) int64 {
	if a >= q {
		return a - q
	}
	return 0
}

// StepM1 is the off-by-one: Confirm accepts when clock <= expiresAt, so at
// clock == expiresAt a Held record is confirmed instead of rejected TooLate.
func StepM1(s core.State, e core.Event) (core.State, []core.Effect) {
	if ri := recOf(s, e, core.Confirm); ri >= 0 && s.Res[ri].Status == core.Held && s.Res[ri].ExpiresAt == s.Clock {
		return confirmApply(s, ri)
	}
	return core.Step(s, e)
}

// StepM1b requires clock > expiresAt for Expire: at clock == expiresAt a Held
// record is rejected NotYet instead of expired.
func StepM1b(s core.State, e core.Event) (core.State, []core.Effect) {
	if ri := recOf(s, e, core.Expire); ri >= 0 && s.Res[ri].Status == core.Held && s.Res[ri].ExpiresAt == s.Clock {
		return clone(s), []core.Effect{{Kind: core.FxRejected, ID: e.ID, Reason: core.NotYet}}
	}
	return core.Step(s, e)
}

// StepM2 is the double release: Expire needs only that the record exists and
// is Due, not that it is Held. Every Due record, whatever its status, gets all
// of S6 again (available += qty, reserved -= qty, returned++, FxReleased).
func StepM2(s core.State, e core.Event) (core.State, []core.Effect) {
	if ri := recOf(s, e, core.Expire); ri >= 0 && core.Due(s, s.Res[ri]) {
		return expireApply(s, ri, false)
	}
	return core.Step(s, e)
}

// StepM3 is Confirm with no status check and no Due check: any existing
// record gets all of S4, so an Expired record becomes Confirmed.
func StepM3(s core.State, e core.Event) (core.State, []core.Effect) {
	if ri := recOf(s, e, core.Confirm); ri >= 0 {
		return confirmApply(s, ri)
	}
	return core.Step(s, e)
}

// StepM3b is Confirm that checks Held but not Due (confirm after the clock passed).
func StepM3b(s core.State, e core.Event) (core.State, []core.Effect) {
	if ri := recOf(s, e, core.Confirm); ri >= 0 && s.Res[ri].Status == core.Held {
		return confirmApply(s, ri)
	}
	return core.Step(s, e)
}

// reserveWellFormed reports an up Reserve that passes BadRequest and UnknownSku
// and returns the stock index; the mutants below differ from core after that.
func reserveWellFormed(s core.State, e core.Event) (int, bool) {
	if !s.Up || e.Kind != core.Reserve || e.Qty < 1 || e.Ttl < 1 {
		return -1, false
	}
	ki := findStock(s, e.Sku)
	return ki, ki >= 0
}

// StepM5 is the unguarded truncated subtraction: Reserve with qty > available
// and a fresh id is accepted, and available := if a >= q { a - q } else { 0 }.
func StepM5(s core.State, e core.Event) (core.State, []core.Effect) {
	if ki, ok := reserveWellFormed(s, e); ok && findRes(s, e.ID) < 0 && e.Qty > s.Stocks[ki].Available {
		return reserveApply(s, ki, e, truncSub)
	}
	return core.Step(s, e)
}

// StepM5a is the unguarded plain subtraction (int64, can go negative). No Bend counterpart.
func StepM5a(s core.State, e core.Event) (core.State, []core.Effect) {
	if ki, ok := reserveWellFormed(s, e); ok && findRes(s, e.ID) < 0 && e.Qty > s.Stocks[ki].Available {
		return reserveApply(s, ki, e, plainSub)
	}
	return core.Step(s, e)
}

// StepM6 is the leak: Expire adds to available but does not reduce reserved.
func StepM6(s core.State, e core.Event) (core.State, []core.Effect) {
	if ri := recOf(s, e, core.Expire); ri >= 0 && s.Res[ri].Status == core.Held && core.Due(s, s.Res[ri]) {
		return expireApply(s, ri, true)
	}
	return core.Step(s, e)
}

// StepM7 accepts a Reserve whose id already exists (any status): it appends a
// second record with the same id, takes qty again (still subject to
// qty <= available) and emits a second FxReserved.
func StepM7(s core.State, e core.Event) (core.State, []core.Effect) {
	if ki, ok := reserveWellFormed(s, e); ok && findRes(s, e.ID) >= 0 && e.Qty <= s.Stocks[ki].Available {
		return reserveApply(s, ki, e, plainSub)
	}
	return core.Step(s, e)
}

// M4State is core.State plus the mutant-only approved list of M4.
// core.State has no such field, and core.go may not be edited.
type M4State struct {
	core.State
	Approved []core.Event
}

// InitM4 builds the empty M4 state.
func InitM4(skus []core.StockInit) M4State { return M4State{State: core.Init(skus)} }

// StepM4 is the check-then-act race. ReserveCheck{id,sku,qty,ttl} (up, qty and
// ttl >= 1, the stock exists, qty <= available) appends the request to
// Approved and changes no counter. ReserveCommit{id} (up) takes the first
// approved request with that id out of the list and applies S2 without
// re-checking anything (no duplicate-id check, no qty <= available check).
// With available 3, Check{1,qty 2}, Check{2,qty 2}, Commit 1, Commit 2 leaves
// available -1. Every other event is core.Step on the embedded state with
// Approved carried unchanged. Down: Check and Commit are lost like any event.
func StepM4(m M4State, e core.Event) (M4State, []core.Effect) {
	app := append([]core.Event(nil), m.Approved...)
	switch {
	case m.Up && e.Kind == ReserveCheck:
		if ki := findStock(m.State, e.Sku); e.Qty >= 1 && e.Ttl >= 1 && ki >= 0 && e.Qty <= m.Stocks[ki].Available {
			app = append(app, e)
		}
		return M4State{clone(m.State), app}, nil
	case m.Up && e.Kind == ReserveCommit:
		for i, a := range app {
			if a.ID == e.ID {
				app = append(app[:i:i], app[i+1:]...)
				t, fx := reserveApply(m.State, findStock(m.State, a.Sku), a, plainSub)
				return M4State{t, app}, fx
			}
		}
		return M4State{clone(m.State), app}, nil
	case e.Kind == ReserveCheck || e.Kind == ReserveCommit: // down: lost (S0)
		return M4State{clone(m.State), app}, nil
	}
	t, fx := core.Step(m.State, e)
	return M4State{t, app}, fx
}

// StepM4Contract is StepM4 seen through the contract alphabet only: Approved
// is not observable in core.State, so it is dropped. It is stateless, so it
// fits a harness StepFn; with no ReserveCheck ever sent it equals core.Step.
func StepM4Contract(s core.State, e core.Event) (core.State, []core.Effect) {
	m, fx := StepM4(M4State{State: s}, e)
	return m.State, fx
}
