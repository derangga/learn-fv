// Package core is the pure UC2 step function (properties/UC2.md sections 2 to 4).
// TLA+ and the Bend port mirror Step; nothing here does I/O or reads a clock.
// Time is the Tick event. Every number is int64 so a buggy Step can go negative.
package core

// Status is the reservation status.
type Status uint8

const (
	Held Status = iota
	Confirmed
	Expired
)

func (x Status) String() string {
	switch x {
	case Held:
		return "Held"
	case Confirmed:
		return "Confirmed"
	case Expired:
		return "Expired"
	}
	return "Status(?)"
}

// Stock is one SKU's counters. All stored, none derived.
type Stock struct {
	Sku, Total, Available, Reserved, Sold int64
}

// Res is one reservation record. ConfirmedAt and Returned are ghost fields.
type Res struct {
	ID, Sku, Qty           int64
	Status                 Status
	ExpiresAt, ConfirmedAt int64
	Returned               int64
}

// State is the whole service state. Reservations keep insertion order.
type State struct {
	Up     bool
	Clock  int64
	Stocks []Stock
	Res    []Res
}

// StockInit is the input of Init for one SKU.
type StockInit struct{ Sku, Total int64 }

// Kind is the event kind. Values follow the contract table order.
type Kind uint8

const (
	Reserve Kind = iota
	Confirm
	Expire
	Tick
	Crash
	Restart
)

var kindNames = [...]string{"Reserve", "Confirm", "Expire", "Tick", "Crash", "Restart"}

func (k Kind) String() string {
	if int(k) < len(kindNames) {
		return kindNames[k]
	}
	return "Kind(?)"
}

// Event is one atomic input to Step. Unused fields are ignored.
type Event struct {
	Kind     Kind
	ID, Sku  int64
	Qty, Ttl int64
}

// EffectKind is the effect kind.
type EffectKind uint8

const (
	FxReserved EffectKind = iota
	FxConfirmed
	FxReleased
	FxRejected
)

var fxNames = [...]string{"FxReserved", "FxConfirmed", "FxReleased", "FxRejected"}

func (k EffectKind) String() string {
	if int(k) < len(fxNames) {
		return fxNames[k]
	}
	return "EffectKind(?)"
}

// Reason is the reject reason carried by FxRejected.
type Reason uint8

const (
	BadRequest Reason = iota
	UnknownSku
	DuplicateId
	InsufficientStock
	UnknownReservation
	NotHeld
	TooLate
	NotYet
)

var reasonNames = [...]string{"BadRequest", "UnknownSku", "DuplicateId", "InsufficientStock",
	"UnknownReservation", "NotHeld", "TooLate", "NotYet"}

func (r Reason) String() string {
	if int(r) < len(reasonNames) {
		return reasonNames[r]
	}
	return "Reason(?)"
}

// Effect is one output. FxReserved uses ID, Sku, Qty, ExpiresAt; FxConfirmed
// uses ID; FxReleased uses ID, Qty; FxRejected uses ID, Reason.
type Effect struct {
	Kind         EffectKind
	ID, Sku, Qty int64
	ExpiresAt    int64
	Reason       Reason
}

// Init gives available = total, reserved = sold = 0, up, clock 0, no records.
func Init(skus []StockInit) State {
	s := State{Up: true, Stocks: make([]Stock, len(skus))}
	for i, k := range skus {
		s.Stocks[i] = Stock{Sku: k.Sku, Total: k.Total, Available: k.Total}
	}
	return s
}

func (s State) clone() State {
	s.Stocks = append([]Stock(nil), s.Stocks...)
	s.Res = append([]Res(nil), s.Res...)
	return s
}

func findStock(s State, sku int64) int {
	for i := range s.Stocks {
		if s.Stocks[i].Sku == sku {
			return i
		}
	}
	return -1
}

func findRes(s State, id int64) int {
	for i := range s.Res {
		if s.Res[i].ID == id {
			return i
		}
	}
	return -1
}

// Due is expiresAt <= clock.
func Due(s State, r Res) bool { return r.ExpiresAt <= s.Clock }

func reject(id int64, c Reason) []Effect {
	return []Effect{{Kind: FxRejected, ID: id, Reason: c}}
}

// Step applies one event. It never mutates its input; a rejected or ignored
// event returns the state unchanged (a copy) with the effects shown.
func Step(s State, e Event) (State, []Effect) {
	s = s.clone()
	if !s.Up && e.Kind != Tick && e.Kind != Restart { // S0
		return s, nil
	}
	switch e.Kind {
	case Tick: // S1, up or down
		s.Clock++
		return s, nil
	case Reserve:
		return reserve(s, e)
	case Confirm:
		return confirm(s, e)
	case Expire:
		return expire(s, e)
	case Crash: // S8
		s.Up = false
		return s, nil
	case Restart: // S9
		s.Up = true
		return s, nil
	}
	return s, nil // unknown kind: Step is total, nothing changes
}

// reserve is S2 and S3. s is already a private copy.
func reserve(s State, e Event) (State, []Effect) {
	if e.Qty < 1 || e.Ttl < 1 {
		return s, reject(e.ID, BadRequest)
	}
	ki := findStock(s, e.Sku)
	if ki < 0 {
		return s, reject(e.ID, UnknownSku)
	}
	if findRes(s, e.ID) >= 0 {
		return s, reject(e.ID, DuplicateId)
	}
	k := &s.Stocks[ki]
	if e.Qty > k.Available {
		return s, reject(e.ID, InsufficientStock)
	}
	exp := s.Clock + e.Ttl
	k.Available -= e.Qty // guard: e.Qty <= k.Available (checked just above)
	k.Reserved += e.Qty
	s.Res = append(s.Res, Res{ID: e.ID, Sku: e.Sku, Qty: e.Qty, Status: Held, ExpiresAt: exp})
	return s, []Effect{{Kind: FxReserved, ID: e.ID, Sku: e.Sku, Qty: e.Qty, ExpiresAt: exp}}
}

// confirm is S4 and S5.
func confirm(s State, e Event) (State, []Effect) {
	ri := findRes(s, e.ID)
	if ri < 0 {
		return s, reject(e.ID, UnknownReservation)
	}
	r := &s.Res[ri]
	if r.Status != Held {
		return s, reject(e.ID, NotHeld)
	}
	if Due(s, *r) {
		return s, reject(e.ID, TooLate) // lazy expiry: stays Held
	}
	ki := findStock(s, r.Sku)
	if ki < 0 { // unreachable under A2; keep Step total
		return s, nil
	}
	k := &s.Stocks[ki]
	k.Reserved -= r.Qty // guard: A1 gives k.Reserved == HeldQty >= r.Qty, r is Held
	k.Sold += r.Qty
	r.Status = Confirmed
	r.ConfirmedAt = s.Clock
	return s, []Effect{{Kind: FxConfirmed, ID: e.ID}}
}

// expire is S6 and S7.
func expire(s State, e Event) (State, []Effect) {
	ri := findRes(s, e.ID)
	if ri < 0 {
		return s, reject(e.ID, UnknownReservation)
	}
	r := &s.Res[ri]
	if r.Status != Held {
		return s, reject(e.ID, NotHeld)
	}
	if !Due(s, *r) {
		return s, reject(e.ID, NotYet)
	}
	ki := findStock(s, r.Sku)
	if ki < 0 { // unreachable under A2; keep Step total
		return s, nil
	}
	k := &s.Stocks[ki]
	k.Reserved -= r.Qty // guard: A1 gives k.Reserved == HeldQty >= r.Qty, r is Held
	k.Available += r.Qty
	r.Status = Expired
	r.Returned++
	return s, []Effect{{Kind: FxReleased, ID: e.ID, Qty: r.Qty}}
}

// ---- Invariants (properties/UC2.md section 3 and 4) ----

// NonNegativeAvailable is P1.
func NonNegativeAvailable(s State) bool {
	for _, k := range s.Stocks {
		if k.Available < 0 {
			return false
		}
	}
	return true
}

// Conservation is P2.
func Conservation(s State) bool {
	for _, k := range s.Stocks {
		if k.Available+k.Reserved+k.Sold != k.Total {
			return false
		}
	}
	return true
}

// ExpiredReturnedOnce is P3.
func ExpiredReturnedOnce(s State) bool {
	for _, r := range s.Res {
		if r.Status == Expired && r.Returned != 1 || r.Status != Expired && r.Returned != 0 {
			return false
		}
	}
	return true
}

// ConfirmedBeforeDue is P4a.
func ConfirmedBeforeDue(s State) bool {
	for _, r := range s.Res {
		if r.Status == Confirmed && r.ConfirmedAt >= r.ExpiresAt {
			return false
		}
	}
	return true
}

// HeldQty and ConfirmedQty sum the qty of the records of one SKU in a status.
func HeldQty(s State, sku int64) int64      { return qtySum(s, sku, Held) }
func ConfirmedQty(s State, sku int64) int64 { return qtySum(s, sku, Confirmed) }

func qtySum(s State, sku int64, st Status) (n int64) {
	for _, r := range s.Res {
		if r.Sku == sku && r.Status == st {
			n += r.Qty
		}
	}
	return n
}

// CountersMatchRecords is A1.
func CountersMatchRecords(s State) bool {
	for _, k := range s.Stocks {
		if k.Reserved != HeldQty(s, k.Sku) || k.Sold != ConfirmedQty(s, k.Sku) {
			return false
		}
	}
	return true
}

// UniqueIdsKnownSku is A2.
func UniqueIdsKnownSku(s State) bool {
	seen := map[int64]bool{}
	for _, r := range s.Res {
		if seen[r.ID] || findStock(s, r.Sku) < 0 {
			return false
		}
		seen[r.ID] = true
	}
	return true
}

// Inv is P1 and P2 and P3 and P4a and A1 and A2.
func Inv(s State) bool {
	return NonNegativeAvailable(s) && Conservation(s) && ExpiredReturnedOnce(s) &&
		ConfirmedBeforeDue(s) && CountersMatchRecords(s) && UniqueIdsKnownSku(s)
}

// ---- Transition and history predicates (P1b, P3b, P4, P4b) ----

func stockOf(s State, sku int64) (Stock, bool) {
	if i := findStock(s, sku); i >= 0 {
		return s.Stocks[i], true
	}
	return Stock{}, false
}

// NoOversell is P1b for one step (s, e) -> (s2, fx).
func NoOversell(s State, e Event, s2 State, fx []Effect) bool {
	for _, k := range s.Stocks {
		k2, ok := stockOf(s2, k.Sku)
		if !ok || k2.Available >= k.Available {
			continue
		}
		want := Effect{Kind: FxReserved, ID: e.ID, Sku: k.Sku, Qty: e.Qty, ExpiresAt: s.Clock + e.Ttl}
		if e.Kind != Reserve || e.Sku != k.Sku || len(fx) != 1 || fx[0] != want || k2.Available+e.Qty != k.Available {
			return false
		}
	}
	return true
}

// ExpiredNeverConfirmed is P4 for one step: an Expired record stays Expired.
func ExpiredNeverConfirmed(s, s2 State) bool {
	for _, r := range s.Res {
		if r.Status != Expired {
			continue
		}
		i := findRes(s2, r.ID)
		if i < 0 || s2.Res[i].Status != Expired {
			return false
		}
	}
	return true
}

// ConfirmOnlyBeforeDue is P4b for one step.
func ConfirmOnlyBeforeDue(s, s2 State) bool {
	for _, r := range s2.Res {
		if r.Status != Confirmed {
			continue
		}
		i := findRes(s, r.ID)
		if i >= 0 && s.Res[i].Status != Confirmed && (s.Res[i].Status != Held || Due(s, s.Res[i])) {
			return false
		}
	}
	return true
}

// ReleasedCount counts FxReleased effects for id.
func ReleasedCount(id int64, fx []Effect) (n int64) {
	for _, f := range fx {
		if f.Kind == FxReleased && f.ID == id {
			n++
		}
	}
	return n
}

// ReleasedMatchesReturned is P3b: for every record, the emitted FxReleased
// count equals r.Returned and each such effect has qty == r.Qty. fx is every
// effect emitted since Init, delivered or not.
func ReleasedMatchesReturned(s State, fx []Effect) bool {
	for _, r := range s.Res {
		if ReleasedCount(r.ID, fx) != r.Returned {
			return false
		}
	}
	for _, f := range fx {
		if f.Kind != FxReleased {
			continue
		}
		i := findRes(s, f.ID)
		if i < 0 || s.Res[i].Qty != f.Qty {
			return false
		}
	}
	return true
}
