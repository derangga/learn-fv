// Package inventory is the UC2 service: a stock-reservation service with its
// own SQLite file and an effect outbox. All business logic is core.Step; this
// package loads the state, calls Step and writes the result back in one
// transaction. Faults come from internal/sim, never from real timing.
package inventory

import (
	"bytes"
	"database/sql"
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"net/http/httptest"
	"path/filepath"
	"time"

	"github.com/derangga/learn-formal-verification/internal/sim"
	"github.com/derangga/learn-formal-verification/internal/uc2/core"
)

// ErrDown is returned for any request to a crashed service (Tick and Restart excepted).
var ErrDown = errors.New("inventory: service down")

// AfterCommit is the crash point checked after every applied request: state
// and outbox rows are committed, the reply has not left.
const AfterCommit = "after-commit"

const (
	name   = "inventory" // Crasher and Net destination of requests
	client = "client"    // Net destination of replies
)

// Config builds a Service. Dir receives inventory.db.
type Config struct {
	Dir       string
	Seed      uint64
	Stocks    []core.StockInit
	Faults    sim.Faults
	Crash     sim.CrashConfig
	Clock     sim.Clock     // nil: a Fake at the zero time
	TickEvery time.Duration // wall time per logical tick (default 1s)
}

// Service is single-threaded and deterministic. Requests reach it by HTTP
// handler (httptest recorder, no sockets) after crossing sim.Net.
type Service struct {
	Trace   *sim.Trace
	path    string
	db      *sql.DB
	cr      *sim.Crasher
	in      *sim.Net[core.Event]  // client -> service
	out     *sim.Net[core.Effect] // service -> client
	h       http.Handler
	clock   sim.Clock
	start   time.Time
	every   time.Duration
	ticks   int64
	log     []core.Event
	replies []core.Effect
}

func New(cfg Config) (*Service, error) {
	s := &Service{Trace: &sim.Trace{}, path: filepath.Join(cfg.Dir, "inventory.db"), every: cfg.TickEvery, clock: cfg.Clock}
	if s.every <= 0 {
		s.every = time.Second
	}
	if s.clock == nil {
		s.clock = sim.NewFake(time.Time{})
	}
	s.start = s.clock.Now()
	s.cr = sim.NewCrasher(cfg.Seed, cfg.Crash, s.Trace)
	s.in = sim.NewNet[core.Event](cfg.Seed, cfg.Faults, s.cr, s.Trace)
	s.out = sim.NewNet[core.Effect](cfg.Seed+1, cfg.Faults, nil, s.Trace)
	if err := s.reopen(); err != nil {
		return nil, err
	}
	tx, err := s.db.Begin()
	if err != nil {
		return nil, err
	}
	defer tx.Rollback()
	if _, ok, err := load(tx); err != nil {
		return nil, err
	} else if !ok {
		if err := save(tx, core.Init(cfg.Stocks), nil); err != nil {
			return nil, err
		}
	}
	if err := tx.Commit(); err != nil {
		return nil, err
	}
	s.h = s.Handler()
	return s, nil
}

// reopen closes and reopens the file: what a process restart sees.
func (s *Service) reopen() error {
	s.Close()
	db, err := openDB(s.path)
	s.db = db
	return err
}

func (s *Service) Close() {
	if s.db != nil {
		s.db.Close()
		s.db = nil
	}
}

// apply is the whole service logic: tx{load; core.Step; save state + outbox}.
// Every event that reaches apply is logged for the differential test, including
// one dropped while down (Step maps it to a no-op, rule S0, so the fold is
// unaffected); such a request then gets ErrDown.
func (s *Service) apply(e core.Event) ([]core.Effect, error) {
	tx, err := s.db.Begin()
	if err != nil {
		return nil, err
	}
	defer tx.Rollback()
	st, _, err := load(tx)
	if err != nil {
		return nil, err
	}
	st2, fx := core.Step(st, e)
	if err := save(tx, st2, fx); err != nil {
		return nil, err
	}
	if err := tx.Commit(); err != nil {
		return nil, err
	}
	s.log = append(s.log, e)
	if !st.Up && e.Kind != core.Tick && e.Kind != core.Restart {
		return nil, ErrDown
	}
	return fx, nil
}

// post sends e through the HTTP handler, then runs the after-commit crash point.
func (s *Service) post(path string, e core.Event) error {
	buf, _ := json.Marshal(body{ID: e.ID, Sku: e.Sku, Qty: e.Qty, Ttl: e.Ttl})
	w := httptest.NewRecorder()
	s.h.ServeHTTP(w, httptest.NewRequest(http.MethodPost, path, bytes.NewReader(buf)))
	switch w.Code {
	case http.StatusOK:
	case http.StatusServiceUnavailable:
		return ErrDown
	default:
		return fmt.Errorf("inventory: %s: %d %s", path, w.Code, w.Body.String())
	}
	if s.cr.ShouldCrash(name, AfterCommit) {
		return s.persistCrash()
	}
	return nil
}

func (s *Service) persistCrash() error {
	if _, err := s.apply(core.Event{Kind: core.Crash}); err != nil {
		return err
	}
	return s.reopen()
}

var paths = map[core.Kind]string{core.Reserve: "/reserve", core.Confirm: "/confirm", core.Expire: "/expire", core.Tick: "/tick"}

// Submit puts a client or timer request (Reserve, Confirm, Expire) on the wire.
func (s *Service) Submit(e core.Event) { s.in.Send(name, e) }

// Next delivers one request copy chosen by the seeded schedule; ok is false when
// the wire is empty. A copy for a crashed service is lost with no effect.
func (s *Service) Next() (ok bool, err error) {
	d, ok := s.in.Next()
	if !ok {
		return false, nil
	}
	return true, s.deliver(d)
}

// DeliverIndex, Drop and Duplicate are the scripted forms of Next.
func (s *Service) DeliverIndex(i int) (ok bool, err error) {
	d, ok := s.in.Deliver(i)
	if !ok {
		return false, nil
	}
	return true, s.deliver(d)
}
func (s *Service) Drop(i int) bool                 { return s.in.Drop(i) }
func (s *Service) Duplicate(i int) bool            { return s.in.Duplicate(i) }
func (s *Service) InFlight() []sim.Msg[core.Event] { return s.in.InFlight() }

func (s *Service) deliver(d sim.Delivery[core.Event]) error {
	if d.Lost {
		return nil
	}
	return s.post(paths[d.Body.Kind], d.Body)
}

// Tick applies one logical tick (up or down).
func (s *Service) Tick() error { return s.post("/tick", core.Event{Kind: core.Tick}) }

// SyncClock sends as many Ticks as the injected clock has advanced since New.
func (s *Service) SyncClock() error {
	for want := int64(s.clock.Now().Sub(s.start) / s.every); s.ticks < want; s.ticks++ {
		if err := s.Tick(); err != nil {
			return err
		}
	}
	return nil
}

// Flush moves every unsent outbox row onto the reply wire and marks it sent, in
// one transaction. It returns ErrDown while crashed; rows survive a crash.
func (s *Service) Flush() (int, error) {
	if !s.cr.Up(name) {
		return 0, ErrDown
	}
	tx, err := s.db.Begin()
	if err != nil {
		return 0, err
	}
	defer tx.Rollback()
	fx, seqs, err := outbox(tx, true)
	if err != nil {
		return 0, err
	}
	for _, q := range seqs {
		if _, err := tx.Exec(`UPDATE outbox SET sent=1 WHERE seq=?`, q); err != nil {
			return 0, err
		}
	}
	if err := tx.Commit(); err != nil {
		return 0, err
	}
	for _, f := range fx {
		s.out.Send(client, f)
	}
	return len(fx), nil
}

// NextReply delivers one reply copy to the client, if any is in flight.
func (s *Service) NextReply() bool {
	d, ok := s.out.Next()
	if ok {
		s.replies = append(s.replies, d.Body)
	}
	return ok
}

// Crash takes the service down if the crash budget allows. The Crash event and
// the new flag are durable; replies not yet flushed stay in the outbox.
func (s *Service) Crash() (bool, error) {
	if !s.cr.Crash(name) {
		return false, nil
	}
	return true, s.persistCrash()
}

// Restart brings the service back; a restart while up is a traced no-op that
// still reaches Step (S9: also when already up).
func (s *Service) Restart() error {
	s.cr.Restart(name)
	if err := s.reopen(); err != nil {
		return err
	}
	_, err := s.apply(core.Event{Kind: core.Restart})
	return err
}

// Snapshot reads the durable state.
func (s *Service) Snapshot() (core.State, error) {
	st, _, err := load(s.db)
	return st, err
}

// Log is the applied events in order. Folding core.Step over it from
// core.Init must give Snapshot.
func (s *Service) Log() []core.Event { return s.log }

// Effects is every effect ever emitted, in order (outbox rows, sent or not).
func (s *Service) Effects() ([]core.Effect, error) {
	fx, _, err := outbox(s.db, false)
	return fx, err
}

// Replies is what the client received over the wire so far.
func (s *Service) Replies() []core.Effect { return s.replies }

// Crashes is how many times the service has crashed.
func (s *Service) Crashes() int { return s.cr.Crashes(name) }
