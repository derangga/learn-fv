package inventory

import (
	"errors"
	"fmt"
	"io"
	"math/rand/v2"
	"net/http"
	"net/http/httptest"
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/derangga/learn-formal-verification/internal/sim"
	"github.com/derangga/learn-formal-verification/internal/uc2/core"
)

var stocks = []core.StockInit{{Sku: 0, Total: 5}, {Sku: 1, Total: 3}}

func must(t *testing.T, err error) {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
}

func newS(t *testing.T, cfg Config) *Service {
	t.Helper()
	cfg.Dir = t.TempDir()
	if cfg.Stocks == nil {
		cfg.Stocks = stocks
	}
	s, err := New(cfg)
	must(t, err)
	t.Cleanup(s.Close)
	return s
}

func snap(t *testing.T, s *Service) core.State {
	t.Helper()
	st, err := s.Snapshot()
	must(t, err)
	return st
}

func stateEq(a, b core.State) bool {
	return a.Up == b.Up && a.Clock == b.Clock && slices.Equal(a.Stocks, b.Stocks) && slices.Equal(a.Res, b.Res)
}

// pump delivers FIFO until the request wire is empty.
func pump(t *testing.T, s *Service) {
	t.Helper()
	for {
		ok, err := s.Next()
		if err != nil && !errors.Is(err, ErrDown) {
			t.Fatal(err)
		}
		if !ok {
			return
		}
	}
}

func reserve(id, sku, qty, ttl int64) core.Event {
	return core.Event{Kind: core.Reserve, ID: id, Sku: sku, Qty: qty, Ttl: ttl}
}

func TestReserveConfirmFlow(t *testing.T) {
	s := newS(t, Config{})
	s.Submit(reserve(1, 0, 2, 3))
	s.Submit(core.Event{Kind: core.Confirm, ID: 1})
	pump(t, s)
	n, err := s.Flush()
	must(t, err)
	for s.NextReply() {
	}
	st := snap(t, s)
	if k := st.Stocks[0]; k.Available != 3 || k.Reserved != 0 || k.Sold != 2 || st.Res[0].Status != core.Confirmed || !core.Inv(st) {
		t.Fatalf("state %+v", st)
	}
	want := []core.Effect{{Kind: core.FxReserved, ID: 1, Sku: 0, Qty: 2, ExpiresAt: 3}, {Kind: core.FxConfirmed, ID: 1}}
	if n != 2 || !slices.Equal(s.Replies(), want) {
		t.Fatalf("flushed %d replies %v", n, s.Replies())
	}
	if n, _ := s.Flush(); n != 0 {
		t.Fatal("rows flushed twice")
	}
}

func TestExpiryByInjectedClock(t *testing.T) {
	clk := sim.NewFake(time.Unix(100, 0))
	s := newS(t, Config{Clock: clk, TickEvery: time.Second})
	s.Submit(reserve(1, 1, 3, 2))
	pump(t, s)
	s.Submit(core.Event{Kind: core.Expire, ID: 1})
	pump(t, s) // clock 0 < expiresAt 2: NotYet
	if st := snap(t, s); st.Res[0].Status != core.Held || st.Stocks[1].Reserved != 3 {
		t.Fatalf("expired early: %+v", st)
	}
	clk.Advance(2500 * time.Millisecond)
	must(t, s.SyncClock())
	must(t, s.SyncClock()) // idempotent
	if st := snap(t, s); st.Clock != 2 {
		t.Fatalf("clock %d, want 2", st.Clock)
	}
	s.Submit(core.Event{Kind: core.Confirm, ID: 1}) // TooLate, stays Held
	s.Submit(core.Event{Kind: core.Expire, ID: 1})
	pump(t, s)
	st := snap(t, s)
	if st.Res[0].Status != core.Expired || st.Res[0].Returned != 1 || st.Stocks[1].Available != 3 || !core.Inv(st) {
		t.Fatalf("state %+v", st)
	}
	fx, err := s.Effects()
	must(t, err)
	rej := func(r core.Reason) core.Effect { return core.Effect{Kind: core.FxRejected, ID: 1, Reason: r} }
	want := []core.Effect{{Kind: core.FxReserved, ID: 1, Sku: 1, Qty: 3, ExpiresAt: 2}, rej(core.NotYet), rej(core.TooLate),
		{Kind: core.FxReleased, ID: 1, Qty: 3}}
	if !slices.Equal(fx, want) {
		t.Fatalf("effects %v", fx)
	}
}

func TestCrashAfterCommitBeforeReply(t *testing.T) {
	s := newS(t, Config{Crash: sim.CrashConfig{MaxCrashes: 1,
		Script: []sim.CrashPoint{{Svc: name, Point: AfterCommit, Nth: 1}}}})
	s.Submit(reserve(1, 0, 4, 5))
	ok, err := s.Next() // commits state + outbox row, then the service crashes
	must(t, err)
	if !ok {
		t.Fatal("nothing delivered")
	}
	if _, err := s.Flush(); !errors.Is(err, ErrDown) {
		t.Fatalf("flush on crashed service: %v", err)
	}
	st := snap(t, s) // durable file survived: state changed, reply not sent
	if st.Up || st.Stocks[0].Reserved != 4 || len(st.Res) != 1 || len(s.Replies()) != 0 {
		t.Fatalf("durable state lost: %+v", st)
	}
	s.Submit(core.Event{Kind: core.Confirm, ID: 1})
	pump(t, s) // delivered to a crashed service: lost
	must(t, s.Tick())
	if st := snap(t, s); st.Clock != 1 || st.Res[0].Status != core.Held {
		t.Fatalf("tick while down or lost confirm wrong: %+v", st)
	}
	must(t, s.Restart())
	if n, err := s.Flush(); err != nil || n != 1 {
		t.Fatalf("outbox after restart: %d %v", n, err)
	}
	s.NextReply()
	if r := s.Replies(); len(r) != 1 || r[0].Kind != core.FxReserved {
		t.Fatalf("replies %v", r)
	}
	// a retried Confirm (the client never saw its first reply) now works
	s.Submit(core.Event{Kind: core.Confirm, ID: 1})
	pump(t, s)
	if st := snap(t, s); st.Res[0].Status != core.Confirmed || !st.Up {
		t.Fatalf("after restart: %+v", st)
	}
}

func TestHTTPBadRequestsAndDown(t *testing.T) {
	s := newS(t, Config{Crash: sim.CrashConfig{MaxCrashes: 1}})
	h := s.Handler()
	for _, c := range []struct {
		path, body string
		code       int
	}{
		{"/reserve", `{`, 400}, {"/confirm", `nope`, 400}, {"/reserve", `{"id":1,"sku":0,"qty":1,"ttl":1}`, 200},
		{"/reserve", `{"id":1,"sku":0,"qty":0,"ttl":1}`, 200}, {"/nosuch", `{}`, 404},
	} {
		w := httptest.NewRecorder()
		h.ServeHTTP(w, httptest.NewRequest(http.MethodPost, c.path, strings.NewReader(c.body)))
		if w.Code != c.code {
			t.Errorf("%s %s: %d, want %d", c.path, c.body, w.Code, c.code)
		}
	}
	if ok, err := s.Crash(); err != nil || !ok {
		t.Fatalf("crash: %v %v", ok, err)
	}
	w := httptest.NewRecorder()
	h.ServeHTTP(w, httptest.NewRequest(http.MethodPost, "/confirm", strings.NewReader(`{"id":1}`)))
	if w.Code != 503 {
		t.Errorf("down: %d, want 503", w.Code)
	}
}

func TestListenLocalOnly(t *testing.T) {
	s := newS(t, Config{})
	if _, _, err := ListenLocal(s.Handler(), "0.0.0.0:0"); err == nil {
		t.Fatal("0.0.0.0 accepted")
	}
	addr, stop, err := ListenLocal(s.Handler(), "127.0.0.1:0")
	must(t, err)
	defer stop()
	resp, err := http.Post(fmt.Sprintf("http://%s/reserve", addr), "application/json",
		strings.NewReader(`{"id":7,"sku":1,"qty":2,"ttl":4}`))
	must(t, err)
	b, _ := io.ReadAll(resp.Body)
	resp.Body.Close()
	if resp.StatusCode != 200 || !strings.Contains(string(b), `"ExpiresAt":4`) {
		t.Fatalf("%d %s", resp.StatusCode, b)
	}
}

// ---- seeded fault runs ----

type counts struct {
	dup, drop, lost, crash, restart, tickDown, reserved, confirmed, released int
	dedupe, tooLate, notYet, insufficient, replyDelivered                    int
}

func (c *counts) add(o counts) {
	c.dup += o.dup
	c.drop += o.drop
	c.lost += o.lost
	c.crash += o.crash
	c.restart += o.restart
	c.tickDown += o.tickDown
	c.reserved += o.reserved
	c.confirmed += o.confirmed
	c.released += o.released
	c.dedupe += o.dedupe
	c.tooLate += o.tooLate
	c.notYet += o.notYet
	c.insufficient += o.insufficient
	c.replyDelivered += o.replyDelivered
}

func (c counts) require(t *testing.T) {
	t.Helper()
	t.Logf("coverage: %+v", c)
	for n, v := range map[string]int{"dup": c.dup, "drop": c.drop, "lost": c.lost, "crash": c.crash, "restart": c.restart,
		"tickDown": c.tickDown, "reserved": c.reserved, "confirmed": c.confirmed, "released": c.released,
		"dedupe": c.dedupe, "tooLate": c.tooLate, "notYet": c.notYet, "insufficient": c.insufficient,
		"replyDelivered": c.replyDelivered} {
		if v == 0 {
			t.Fatalf("vacuous: %q never happened", n)
		}
	}
}

// faultRun drives one seeded run and calls check after every action.
func faultRun(t *testing.T, seed uint64, steps int, check func(s *Service, st core.State)) counts {
	t.Helper()
	clk := sim.NewFake(time.Unix(0, 0))
	s := newS(t, Config{Seed: seed, Clock: clk,
		Faults: sim.Faults{Drop: 0.15, Dup: 0.15, MaxDup: 2, Reorder: true},
		Crash:  sim.CrashConfig{Prob: 0.05, MaxCrashes: 3}})
	r := rand.New(rand.NewPCG(seed, 0x1fe))
	var c counts
	okErr := func(err error) {
		if err != nil && !errors.Is(err, ErrDown) {
			t.Fatalf("seed %d: %v", seed, err)
		}
	}
	for i := 0; i < steps; i++ {
		switch n := r.IntN(100); {
		case n < 30:
			s.Submit(reserve(int64(1+r.IntN(8)), int64(r.IntN(3)), int64(r.IntN(5)), int64(r.IntN(4))))
		case n < 40:
			s.Submit(core.Event{Kind: core.Confirm, ID: int64(1 + r.IntN(8))})
		case n < 50:
			s.Submit(core.Event{Kind: core.Expire, ID: int64(1 + r.IntN(8))})
		case n < 75:
			_, err := s.Next()
			okErr(err)
		case n < 85:
			clk.Advance(time.Second)
			if st := snap(t, s); !st.Up {
				c.tickDown++
			}
			okErr(s.SyncClock())
		case n < 90:
			_, err := s.Flush()
			okErr(err)
		case n < 95:
			s.NextReply()
		case n < 97:
			_, err := s.Crash()
			okErr(err)
		default:
			okErr(s.Restart())
		}
		check(s, snap(t, s))
	}
	for _, e := range s.Trace.Entries {
		switch e.Kind {
		case "dup":
			c.dup++
		case "drop":
			c.drop++
		case "lost":
			if e.Svc == name {
				c.lost++
			}
		case "crash":
			c.crash++
		case "restart":
			c.restart++
		}
	}
	fx, err := s.Effects()
	must(t, err)
	for _, f := range fx {
		switch {
		case f.Kind == core.FxReserved:
			c.reserved++
		case f.Kind == core.FxConfirmed:
			c.confirmed++
		case f.Kind == core.FxReleased:
			c.released++
		case f.Reason == core.NotHeld || f.Reason == core.DuplicateId:
			c.dedupe++
		case f.Reason == core.TooLate:
			c.tooLate++
		case f.Reason == core.NotYet:
			c.notYet++
		case f.Reason == core.InsufficientStock:
			c.insufficient++
		}
	}
	c.replyDelivered = len(s.Replies())
	return c
}

// P1, P2 and Inv hold on the persisted state after every action, and every
// emitted FxReleased is matched by the record's returned counter (P3b).
func TestInvUnderFaultRuns(t *testing.T) {
	var total counts
	for seed := uint64(1); seed <= 150; seed++ {
		total.add(faultRun(t, seed, 150, func(s *Service, st core.State) {
			if !core.NonNegativeAvailable(st) || !core.Conservation(st) || !core.Inv(st) {
				t.Fatalf("seed %d: Inv broken: %+v", seed, st)
			}
			if fx, err := s.Effects(); err != nil || !core.ReleasedMatchesReturned(st, fx) {
				t.Fatalf("seed %d: P3b: %v %v", seed, err, fx)
			}
		}))
	}
	total.require(t)
}

// The persisted state equals the fold of core.Step over the events the
// service applied, from core.Init.
func TestDifferentialAgainstCoreFold(t *testing.T) {
	var total counts
	for seed := uint64(1001); seed <= 1100; seed++ {
		var last *Service
		total.add(faultRun(t, seed, 150, func(s *Service, _ core.State) { last = s }))
		want := core.Init(stocks)
		var wantFx []core.Effect
		for _, e := range last.Log() {
			var fx []core.Effect
			want, fx = core.Step(want, e)
			wantFx = append(wantFx, fx...)
		}
		got, err := last.Snapshot()
		must(t, err)
		if !stateEq(got, want) {
			t.Fatalf("seed %d: snapshot %+v != fold %+v", seed, got, want)
		}
		if fx, err := last.Effects(); err != nil || !slices.Equal(fx, wantFx) {
			t.Fatalf("seed %d: outbox rows differ from folded effects (%v)", seed, err)
		}
	}
	total.require(t)
}
