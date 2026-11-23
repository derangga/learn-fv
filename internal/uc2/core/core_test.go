package core

import (
	"math/rand/v2"
	"slices"
	"testing"
)

const (
	nSeq   = 1000
	maxLen = 150
)

// ---- helpers ----

func stateEq(a, b State) bool {
	return a.Up == b.Up && a.Clock == b.Clock && slices.Equal(a.Stocks, b.Stocks) && slices.Equal(a.Res, b.Res)
}

func fxEq(a, b []Effect) bool { return slices.Equal(a, b) }

func rej(id int64, c Reason) []Effect { return []Effect{{Kind: FxRejected, ID: id, Reason: c}} }

// gen holds one seeded sequence generator.
type gen struct {
	r    *rand.Rand
	nsku int64
	maxT int64
	prev []Event
}

func (g *gen) init() State {
	g.nsku = int64(1 + g.r.IntN(3))
	g.maxT = 6
	g.prev = nil
	in := make([]StockInit, g.nsku)
	for i := range in {
		in[i] = StockInit{Sku: int64(i), Total: int64(1 + g.r.IntN(int(g.maxT)))}
	}
	return Init(in)
}

// event draws any event: sku may be unknown, qty and ttl may be 0, and
// earlier events are re-sent (duplicate and reorder) a fraction of the time.
func (g *gen) event() Event {
	if len(g.prev) > 0 && g.r.IntN(100) < 20 {
		return g.prev[g.r.IntN(len(g.prev))]
	}
	e := Event{
		ID:  int64(1 + g.r.IntN(6)),
		Sku: int64(g.r.IntN(int(g.nsku) + 1)), // nsku itself is unknown
		Qty: int64(g.r.IntN(int(g.maxT) + 2)),
		Ttl: int64(g.r.IntN(4)),
	}
	switch n := g.r.IntN(100); {
	case n < 30:
		e.Kind = Reserve
	case n < 50:
		e.Kind = Confirm
	case n < 70:
		e.Kind = Expire
	case n < 90:
		e.Kind = Tick
	case n < 94:
		e.Kind = Crash
	default:
		e.Kind = Restart
	}
	g.prev = append(g.prev, e)
	return e
}

// cover counts how often each guarded branch fired.
type cover map[string]int

var coverKeys = []string{
	"down-dropped-Reserve", "down-dropped-Confirm", "down-dropped-Expire", "down-dropped-Crash",
	"crash-while-down", "restart-while-up", "tick-down", "crash", "restart",
	"reserve-ok", "reserve-qty=avail", "rej-BadRequest", "rej-UnknownSku", "rej-DuplicateId", "rej-InsufficientStock",
	"confirm-ok", "confirm-UnknownReservation", "confirm-NotHeld", "confirm-TooLate", "confirm-on-Expired",
	"expire-ok", "expire-UnknownReservation", "expire-NotHeld", "expire-NotYet", "expire-on-Expired", "expire-after-confirm",
	"multi-sku-frame",
}

func (c cover) observe(s State, e Event, s2 State, fx []Effect) {
	if !s.Up && e.Kind != Tick && e.Kind != Restart {
		c["down-dropped-"+e.Kind.String()]++
		if e.Kind == Crash {
			c["crash-while-down"]++
		}
		return
	}
	if s.Up && e.Kind == Restart {
		c["restart-while-up"]++
	}
	one := func(k EffectKind) bool { return len(fx) == 1 && fx[0].Kind == k }
	reason := func(r Reason) bool { return one(FxRejected) && fx[0].Reason == r }
	switch e.Kind {
	case Tick:
		if !s.Up {
			c["tick-down"]++
		}
	case Crash:
		c["crash"]++
	case Restart:
		c["restart"]++
	case Reserve:
		if one(FxReserved) {
			c["reserve-ok"]++
			if i := findStock(s, e.Sku); s.Stocks[i].Available == e.Qty {
				c["reserve-qty=avail"]++
			}
			if len(s.Stocks) > 1 {
				c["multi-sku-frame"]++
			}
		}
		for r, key := range map[Reason]string{BadRequest: "rej-BadRequest", UnknownSku: "rej-UnknownSku",
			DuplicateId: "rej-DuplicateId", InsufficientStock: "rej-InsufficientStock"} {
			if reason(r) {
				c[key]++
			}
		}
	case Confirm:
		if one(FxConfirmed) {
			c["confirm-ok"]++
		}
		if reason(UnknownReservation) {
			c["confirm-UnknownReservation"]++
		}
		if reason(NotHeld) {
			c["confirm-NotHeld"]++
		}
		if reason(TooLate) {
			c["confirm-TooLate"]++
		}
		if i := findRes(s, e.ID); i >= 0 && s.Res[i].Status == Expired {
			c["confirm-on-Expired"]++
		}
	case Expire:
		if one(FxReleased) {
			c["expire-ok"]++
		}
		if reason(UnknownReservation) {
			c["expire-UnknownReservation"]++
		}
		if reason(NotHeld) {
			c["expire-NotHeld"]++
		}
		if reason(NotYet) {
			c["expire-NotYet"]++
		}
		if i := findRes(s, e.ID); i >= 0 {
			switch s.Res[i].Status {
			case Expired:
				c["expire-on-Expired"]++
			case Confirmed:
				c["expire-after-confirm"]++
			}
		}
	}
}

func (c cover) require(t *testing.T) {
	t.Helper()
	t.Logf("coverage: %v", map[string]int(c))
	for _, k := range coverKeys {
		if c[k] == 0 {
			t.Fatalf("vacuous: branch %q never fired", k)
		}
	}
}

// forRuns calls f for every step of the seeded random runs, checks that Step
// did not mutate its input, and requires every branch to have fired. all is
// every effect emitted since Init in the run, including this step's.
func forRuns(t *testing.T, seed uint64, f func(s State, e Event, s2 State, fx, all []Effect)) {
	t.Helper()
	c := cover{}
	r := rand.New(rand.NewPCG(seed, seed^0x9e3779b97f4a7c15))
	g := &gen{r: r}
	for i := 0; i < nSeq; i++ {
		s := g.init()
		var all []Effect
		for j, l := 0, r.IntN(maxLen+1); j < l; j++ {
			e := g.event()
			before := s.clone()
			s2, fx := Step(s, e)
			if !stateEq(before, s) {
				t.Fatalf("Step mutated its input on %v", e)
			}
			all = append(all, fx...)
			c.observe(s, e, s2, fx)
			f(s, e, s2, fx, all)
			s = s2
		}
	}
	c.require(t)
}

func one(s State, e Event) (State, []Effect) { return Step(s, e) }

// ---- Init and invariants ----

func TestInitSatisfiesInv(t *testing.T) {
	for _, in := range [][]StockInit{nil, {{0, 0}}, {{0, 3}, {7, 1}}} {
		s := Init(in)
		if !Inv(s) || !s.Up || s.Clock != 0 || len(s.Res) != 0 {
			t.Fatalf("Init(%v) = %+v", in, s)
		}
		for _, k := range s.Stocks {
			if k.Available != k.Total || k.Reserved != 0 || k.Sold != 0 {
				t.Fatalf("stock %+v", k)
			}
		}
	}
	// Each predicate must reject a hand-built bad state (guards the oracle).
	st := func(m func(*State)) State {
		s := Init([]StockInit{{0, 3}})
		s.Res = []Res{{ID: 1, Sku: 0, Qty: 1, Status: Held, ExpiresAt: 5}}
		s.Stocks[0].Available, s.Stocks[0].Reserved = 2, 1
		m(&s)
		return s
	}
	bad := map[string]struct {
		s State
		p func(State) bool
	}{
		"P1":  {st(func(s *State) { s.Stocks[0].Available = -1; s.Stocks[0].Reserved = 4 }), NonNegativeAvailable},
		"P2":  {st(func(s *State) { s.Stocks[0].Available = 3 }), Conservation},
		"P3a": {st(func(s *State) { s.Res[0].Status = Expired }), ExpiredReturnedOnce},
		"P3b": {st(func(s *State) { s.Res[0].Returned = 1 }), ExpiredReturnedOnce},
		"P4a": {st(func(s *State) { s.Res[0].Status, s.Res[0].ConfirmedAt = Confirmed, 5 }), ConfirmedBeforeDue},
		"A1":  {st(func(s *State) { s.Stocks[0].Reserved, s.Stocks[0].Sold = 0, 1 }), CountersMatchRecords},
		"A2a": {st(func(s *State) { s.Res = append(s.Res, s.Res[0]) }), UniqueIdsKnownSku},
		"A2b": {st(func(s *State) { s.Res[0].Sku = 9 }), UniqueIdsKnownSku},
	}
	for n, b := range bad {
		if b.p(b.s) || Inv(b.s) {
			t.Errorf("bad case %s accepted", n)
		}
	}
	if !Inv(st(func(*State) {})) {
		t.Fatal("good hand-built state rejected")
	}
}

func TestP1NonNegativeAvailable(t *testing.T) {
	forRuns(t, 1, func(_ State, e Event, s2 State, _, _ []Effect) {
		if !NonNegativeAvailable(s2) {
			t.Fatalf("after %v: %+v", e, s2)
		}
	})
}

// TestInvHolds checks the whole conjunction after every step.
func TestInvHolds(t *testing.T) {
	forRuns(t, 23, func(_ State, e Event, s2 State, _, _ []Effect) {
		if !Inv(s2) {
			t.Fatalf("Inv broken after %v: %+v", e, s2)
		}
	})
}

func TestP2Conservation(t *testing.T) {
	forRuns(t, 2, func(_ State, e Event, s2 State, _, _ []Effect) {
		if !Conservation(s2) {
			t.Fatalf("after %v: %+v", e, s2)
		}
	})
}

func TestP3ExpiredReturnsOnce(t *testing.T) {
	forRuns(t, 3, func(_ State, e Event, s2 State, _, _ []Effect) {
		if !ExpiredReturnedOnce(s2) {
			t.Fatalf("after %v: %+v", e, s2.Res)
		}
	})
}

func TestP4ExpiredNeverConfirmed(t *testing.T) {
	forRuns(t, 4, func(s State, e Event, s2 State, _, _ []Effect) {
		if !ExpiredNeverConfirmed(s, s2) {
			t.Fatalf("%v revived an Expired record", e)
		}
	})
}

func TestP1bNoOversell(t *testing.T) {
	forRuns(t, 5, func(s State, e Event, s2 State, fx, _ []Effect) {
		if !NoOversell(s, e, s2, fx) {
			t.Fatalf("%v: stock taken without an accepted Reserve", e)
		}
	})
}

func TestP3bReleasedEffectCount(t *testing.T) {
	forRuns(t, 6, func(_ State, e Event, s2 State, _, all []Effect) {
		if !ReleasedMatchesReturned(s2, all) {
			t.Fatalf("after %v: released effects disagree with returned", e)
		}
	})
}

func TestP4aConfirmedBeforeDue(t *testing.T) {
	forRuns(t, 7, func(_ State, e Event, s2 State, _, _ []Effect) {
		if !ConfirmedBeforeDue(s2) {
			t.Fatalf("after %v: %+v", e, s2.Res)
		}
	})
}

func TestP4bConfirmOnlyBeforeDue(t *testing.T) {
	forRuns(t, 8, func(s State, e Event, s2 State, _, _ []Effect) {
		if !ConfirmOnlyBeforeDue(s, s2) {
			t.Fatalf("%v confirmed a non-Held or Due record", e)
		}
	})
}

func TestA1CountersMatchRecords(t *testing.T) {
	forRuns(t, 9, func(_ State, e Event, s2 State, _, _ []Effect) {
		if !CountersMatchRecords(s2) {
			t.Fatalf("after %v: %+v", e, s2)
		}
	})
}

func TestA2UniqueIds(t *testing.T) {
	forRuns(t, 10, func(_ State, e Event, s2 State, _, _ []Effect) {
		if !UniqueIdsKnownSku(s2) {
			t.Fatalf("after %v: %+v", e, s2.Res)
		}
	})
}

// ---- Pins (S0 to S11) ----

func TestPinDown(t *testing.T) {
	forRuns(t, 11, func(s State, e Event, s2 State, fx, _ []Effect) {
		if !s.Up && e.Kind != Tick && e.Kind != Restart && (!stateEq(s, s2) || fx != nil) {
			t.Fatalf("%v while down changed something", e)
		}
	})
}

func TestPinTick(t *testing.T) {
	forRuns(t, 12, func(s State, e Event, s2 State, fx, _ []Effect) {
		if e.Kind != Tick {
			return
		}
		want := s.clone()
		want.Clock = s.Clock + 1
		if !stateEq(want, s2) || fx != nil {
			t.Fatalf("Tick up=%v: %+v -> %+v fx=%v", s.Up, s, s2, fx)
		}
	})
}

// accepts is the S2 guard, written out independently of Step.
func accepts(s State, e Event) (k int, ok bool) {
	k = findStock(s, e.Sku)
	return k, e.Qty >= 1 && e.Ttl >= 1 && k >= 0 && findRes(s, e.ID) < 0 && e.Qty <= s.Stocks[k].Available
}

func TestPinReserveOk(t *testing.T) {
	forRuns(t, 13, func(s State, e Event, s2 State, fx, _ []Effect) {
		if !s.Up || e.Kind != Reserve {
			return
		}
		ki, ok := accepts(s, e)
		if !ok {
			return
		}
		want := s.clone()
		want.Stocks[ki].Available = s.Stocks[ki].Available - e.Qty
		want.Stocks[ki].Reserved = s.Stocks[ki].Reserved + e.Qty
		want.Res = append(want.Res, Res{ID: e.ID, Sku: e.Sku, Qty: e.Qty, Status: Held, ExpiresAt: s.Clock + e.Ttl})
		wfx := []Effect{{Kind: FxReserved, ID: e.ID, Sku: e.Sku, Qty: e.Qty, ExpiresAt: s.Clock + e.Ttl}}
		if !stateEq(want, s2) || !fxEq(wfx, fx) {
			t.Fatalf("%v: got %+v %v, want %+v %v", e, s2, fx, want, wfx)
		}
	})
}

func TestPinReserveRejected(t *testing.T) {
	forRuns(t, 14, func(s State, e Event, s2 State, fx, _ []Effect) {
		if !s.Up || e.Kind != Reserve {
			return
		}
		if _, ok := accepts(s, e); ok {
			return
		}
		var c Reason
		switch ki := findStock(s, e.Sku); {
		case e.Qty < 1 || e.Ttl < 1:
			c = BadRequest
		case ki < 0:
			c = UnknownSku
		case findRes(s, e.ID) >= 0:
			c = DuplicateId
		default:
			c = InsufficientStock
		}
		if !stateEq(s, s2) || !fxEq(rej(e.ID, c), fx) {
			t.Fatalf("%v: got %v, want %v unchanged", e, fx, c)
		}
	})
	// Boundary: qty == available accepted, available+1 rejected.
	s := Init([]StockInit{{0, 3}})
	if s2, fx := one(s, Event{Kind: Reserve, ID: 1, Sku: 0, Qty: 3, Ttl: 1}); len(fx) != 1 || fx[0].Kind != FxReserved || s2.Stocks[0].Available != 0 {
		t.Fatalf("qty == available: %v %+v", fx, s2)
	}
	if s2, fx := one(s, Event{Kind: Reserve, ID: 1, Sku: 0, Qty: 4, Ttl: 1}); !fxEq(fx, rej(1, InsufficientStock)) || !stateEq(s, s2) {
		t.Fatalf("qty == available+1: %v", fx)
	}
	// Check order: every failure at once gives BadRequest, then UnknownSku, then DuplicateId.
	s, _ = one(s, Event{Kind: Reserve, ID: 1, Sku: 0, Qty: 1, Ttl: 1})
	for _, c := range []struct {
		e Event
		r Reason
	}{
		{Event{Kind: Reserve, ID: 1, Sku: 9, Qty: 0, Ttl: 1}, BadRequest},
		{Event{Kind: Reserve, ID: 1, Sku: 9, Qty: 99, Ttl: 0}, BadRequest},
		{Event{Kind: Reserve, ID: 1, Sku: 9, Qty: 99, Ttl: 1}, UnknownSku},
		{Event{Kind: Reserve, ID: 1, Sku: 0, Qty: 99, Ttl: 1}, DuplicateId},
		{Event{Kind: Reserve, ID: 2, Sku: 0, Qty: 99, Ttl: 1}, InsufficientStock},
	} {
		if _, fx := one(s, c.e); !fxEq(fx, rej(c.e.ID, c.r)) {
			t.Errorf("%v: got %v want %v", c.e, fx, c.r)
		}
	}
}

func TestPinConfirmOk(t *testing.T) {
	forRuns(t, 15, func(s State, e Event, s2 State, fx, _ []Effect) {
		if !s.Up || e.Kind != Confirm {
			return
		}
		ri := findRes(s, e.ID)
		if ri < 0 || s.Res[ri].Status != Held || s.Res[ri].ExpiresAt <= s.Clock {
			return
		}
		r, ki := s.Res[ri], findStock(s, s.Res[ri].Sku)
		want := s.clone()
		want.Res[ri].Status, want.Res[ri].ConfirmedAt = Confirmed, s.Clock
		want.Stocks[ki].Reserved = s.Stocks[ki].Reserved - r.Qty
		want.Stocks[ki].Sold = s.Stocks[ki].Sold + r.Qty
		wfx := []Effect{{Kind: FxConfirmed, ID: e.ID}}
		if !stateEq(want, s2) || !fxEq(wfx, fx) {
			t.Fatalf("%v: got %+v %v", e, s2, fx)
		}
	})
}

func TestPinConfirmRejected(t *testing.T) {
	forRuns(t, 16, func(s State, e Event, s2 State, fx, _ []Effect) {
		if !s.Up || e.Kind != Confirm {
			return
		}
		var c Reason
		switch ri := findRes(s, e.ID); {
		case ri < 0:
			c = UnknownReservation
		case s.Res[ri].Status != Held:
			c = NotHeld
		case s.Res[ri].ExpiresAt <= s.Clock:
			c = TooLate
		default:
			return
		}
		if !stateEq(s, s2) || !fxEq(rej(e.ID, c), fx) {
			t.Fatalf("%v: got %v want %v", e, fx, c)
		}
	})
	// Boundary: Confirm at clock == expiresAt is TooLate and the record stays Held.
	s, _ := one(Init([]StockInit{{0, 3}}), Event{Kind: Reserve, ID: 1, Sku: 0, Qty: 1, Ttl: 2})
	s, _ = one(s, Event{Kind: Tick})
	if _, fx := one(s, Event{Kind: Confirm, ID: 1}); len(fx) != 1 || fx[0].Kind != FxConfirmed {
		t.Fatalf("clock = expiresAt-1: %v", fx)
	}
	s, _ = one(s, Event{Kind: Tick})
	s2, fx := one(s, Event{Kind: Confirm, ID: 1})
	if !fxEq(fx, rej(1, TooLate)) || !stateEq(s, s2) || s2.Res[0].Status != Held {
		t.Fatalf("clock = expiresAt: %v %+v", fx, s2.Res)
	}
}

func TestPinExpireOk(t *testing.T) {
	forRuns(t, 17, func(s State, e Event, s2 State, fx, _ []Effect) {
		if !s.Up || e.Kind != Expire {
			return
		}
		ri := findRes(s, e.ID)
		if ri < 0 || s.Res[ri].Status != Held || s.Res[ri].ExpiresAt > s.Clock {
			return
		}
		r, ki := s.Res[ri], findStock(s, s.Res[ri].Sku)
		want := s.clone()
		want.Res[ri].Status, want.Res[ri].Returned = Expired, r.Returned+1
		want.Stocks[ki].Available = s.Stocks[ki].Available + r.Qty
		want.Stocks[ki].Reserved = s.Stocks[ki].Reserved - r.Qty
		wfx := []Effect{{Kind: FxReleased, ID: e.ID, Qty: r.Qty}}
		if !stateEq(want, s2) || !fxEq(wfx, fx) {
			t.Fatalf("%v: got %+v %v", e, s2, fx)
		}
	})
}

func TestPinExpireRejected(t *testing.T) {
	forRuns(t, 18, func(s State, e Event, s2 State, fx, _ []Effect) {
		if !s.Up || e.Kind != Expire {
			return
		}
		var c Reason
		switch ri := findRes(s, e.ID); {
		case ri < 0:
			c = UnknownReservation
		case s.Res[ri].Status != Held:
			c = NotHeld
		case s.Res[ri].ExpiresAt > s.Clock:
			c = NotYet
		default:
			return
		}
		if !stateEq(s, s2) || !fxEq(rej(e.ID, c), fx) {
			t.Fatalf("%v: got %v want %v", e, fx, c)
		}
	})
	// Boundary: Expire at clock == expiresAt-1 is NotYet, at expiresAt it is accepted.
	s, _ := one(Init([]StockInit{{0, 3}}), Event{Kind: Reserve, ID: 1, Sku: 0, Qty: 1, Ttl: 2})
	s, _ = one(s, Event{Kind: Tick})
	if _, fx := one(s, Event{Kind: Expire, ID: 1}); !fxEq(fx, rej(1, NotYet)) {
		t.Fatalf("early: %v", fx)
	}
	s, _ = one(s, Event{Kind: Tick})
	if _, fx := one(s, Event{Kind: Expire, ID: 1}); len(fx) != 1 || fx[0].Kind != FxReleased {
		t.Fatalf("at expiresAt: %v", fx)
	}
}

func TestPinCrash(t *testing.T) {
	forRuns(t, 19, func(s State, e Event, s2 State, fx, _ []Effect) {
		if e.Kind != Crash {
			return
		}
		want := s.clone()
		want.Up = false
		if !stateEq(want, s2) || fx != nil {
			t.Fatalf("Crash up=%v: %+v fx=%v", s.Up, s2, fx)
		}
	})
}

func TestPinRestart(t *testing.T) {
	forRuns(t, 20, func(s State, e Event, s2 State, fx, _ []Effect) {
		if e.Kind != Restart {
			return
		}
		want := s.clone()
		want.Up = true
		if !stateEq(want, s2) || fx != nil {
			t.Fatalf("Restart up=%v: %+v fx=%v", s.Up, s2, fx)
		}
	})
}

func TestPinStable(t *testing.T) {
	forRuns(t, 21, func(s State, e Event, s2 State, _, _ []Effect) {
		if len(s2.Stocks) != len(s.Stocks) || len(s2.Res) < len(s.Res) {
			t.Fatalf("%v: lists shrank or stocks changed length", e)
		}
		for i, k := range s.Stocks {
			if s2.Stocks[i].Total != k.Total || s2.Stocks[i].Sku != k.Sku {
				t.Fatalf("%v: stock %d identity changed", e, i)
			}
		}
		for i, r := range s.Res {
			r2 := s2.Res[i]
			if r2.ID != r.ID || r2.Sku != r.Sku || r2.Qty != r.Qty || r2.ExpiresAt != r.ExpiresAt {
				t.Fatalf("%v: record %d fields changed", e, i)
			}
			if r.Status != Held && r2.Status != r.Status {
				t.Fatalf("%v: %v record %d changed status", e, r.Status, i)
			}
		}
	})
}

func TestPinDuplicateDelivery(t *testing.T) {
	accepted := map[Kind]int{}
	forRuns(t, 22, func(s State, e Event, s2 State, fx, _ []Effect) {
		if e.Kind != Reserve && e.Kind != Confirm && e.Kind != Expire {
			return
		}
		if s.Up && len(fx) == 1 && (fx[0].Kind == FxReserved || fx[0].Kind == FxConfirmed || fx[0].Kind == FxReleased) {
			accepted[e.Kind]++ // first delivery accepted
		}
		if s3, _ := Step(s2, e); !stateEq(s2, s3) {
			t.Fatalf("second delivery of %v changed state: %+v -> %+v", e, s2, s3)
		}
	})
	t.Logf("first delivery accepted: Reserve=%d Confirm=%d Expire=%d", accepted[Reserve], accepted[Confirm], accepted[Expire])
	for _, k := range []Kind{Reserve, Confirm, Expire} {
		if accepted[k] == 0 {
			t.Fatalf("vacuous: no accepted %v whose duplicate was checked", k)
		}
	}
}
