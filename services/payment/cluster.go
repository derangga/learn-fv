package payment

import (
	"bytes"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"path/filepath"

	"github.com/derangga/learn-formal-verification/internal/sim"
	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

// AfterCommit is the crash point checked after every applied request: the
// outbox row is committed and the message is not yet flushed or delivered.
const AfterCommit = "after-commit"

// Config builds a Cluster. Dir receives order.db and provider.db.
type Config struct {
	N      uint32
	Dir    string
	Seed   uint64
	Faults sim.Faults
	Crash  sim.CrashConfig
	Issuer Issuer // nil means always Approve
}

// Cluster is the in-process, single-threaded driver. Every action goes through
// the service's HTTP handler by direct call (httptest recorder, no sockets).
// Wire* effects go into sim.Net; Deliver* pulls a copy out and POSTs it.
type Cluster struct {
	N     uint32
	Trace *sim.Trace
	cr    *sim.Crasher
	net   *sim.Net[core.Effect]
	order *OrderSvc
	prov  *ProvSvc
	oh    http.Handler
	ph    http.Handler
	log   []core.Event
}

type allApprove struct{}

func (allApprove) Decide(uint32) core.Decision { return core.Approve }

func NewCluster(cfg Config) (*Cluster, error) {
	c := &Cluster{N: cfg.N, Trace: &sim.Trace{}}
	c.cr = sim.NewCrasher(cfg.Seed, cfg.Crash, c.Trace)
	c.net = sim.NewNet[core.Effect](cfg.Seed, cfg.Faults, c.cr, c.Trace)
	is := cfg.Issuer
	if is == nil {
		is = allApprove{}
	}
	c.order = newOrderSvc(filepath.Join(cfg.Dir, "order.db"), cfg.N, c.cr)
	c.prov = newProvSvc(filepath.Join(cfg.Dir, "provider.db"), cfg.N, c.cr, is)
	for _, b := range []*base{&c.order.base, &c.prov.base} {
		b.send = c.send
		b.onApply = func(e core.Event) { c.log = append(c.log, e) }
		if err := b.open(); err != nil {
			c.Close()
			return nil, err
		}
	}
	c.oh, c.ph = c.order.Handler(), c.prov.Handler()
	return c, nil
}

func (c *Cluster) Close() { c.order.close(); c.prov.close() }

// Log is the sequence of events the services applied (Crash and Restart
// included), in order. Folding core.Step over it from core.Init(N) must give
// Snapshot.
func (c *Cluster) Log() []core.Event { return c.log }

func dest(k core.EffectKind) string {
	if k == core.WireChargeReq || k == core.WireRefundReq {
		return core.Provider.String()
	}
	return core.OrderSvc.String()
}

func (c *Cluster) send(f core.Effect) { c.net.Send(dest(f.Kind), f) }

func (c *Cluster) svc(s core.Service) *base {
	if s == core.OrderSvc {
		return &c.order.base
	}
	return &c.prov.base
}

// post is one HTTP call into a service, then the after-commit crash point.
func (c *Cluster) post(h http.Handler, name, path string, b Body) error {
	buf, err := json.Marshal(b)
	if err != nil {
		return err
	}
	w := httptest.NewRecorder()
	h.ServeHTTP(w, httptest.NewRequest(http.MethodPost, path, bytes.NewReader(buf)))
	switch w.Code {
	case http.StatusOK:
	case http.StatusServiceUnavailable:
		return ErrDown
	default:
		return fmt.Errorf("payment: %s %s: %d %s", name, path, w.Code, w.Body.String())
	}
	if c.cr.ShouldCrash(name, AfterCommit) {
		c.downed(name)
	}
	return nil
}

func (c *Cluster) downed(name string) {
	if name == core.OrderSvc.String() {
		c.order.close()
		c.log = append(c.log, core.Event{Kind: core.Crash, Svc: core.OrderSvc})
	} else {
		c.prov.close()
		c.log = append(c.log, core.Event{Kind: core.Crash, Svc: core.Provider})
	}
}

func (c *Cluster) toOrder(path string, b Body) error {
	return c.post(c.oh, core.OrderSvc.String(), path, b)
}
func (c *Cluster) toProv(path string, b Body) error {
	return c.post(c.ph, core.Provider.String(), path, b)
}

// Client events and flushes. Each returns ErrDown if the service is crashed.
func (c *Cluster) PlaceOrder(o, a uint32) error     { return c.toOrder("/place", Body{o, a}) }
func (c *Cluster) RetryTimeout(o uint32) error      { return c.toOrder("/retry", Body{O: o}) }
func (c *Cluster) RefundOrder(o uint32) error       { return c.toOrder("/refund", Body{O: o}) }
func (c *Cluster) FlushCharge(o uint32) error       { return c.toOrder("/flush/charge", Body{O: o}) }
func (c *Cluster) FlushRefund(o uint32) error       { return c.toOrder("/flush/refund", Body{O: o}) }
func (c *Cluster) FlushReply(o uint32) error        { return c.toProv("/flush/reply", Body{O: o}) }
func (c *Cluster) InFlight() []sim.Msg[core.Effect] { return c.net.InFlight() }
func (c *Cluster) Drop(i int) bool                  { return c.net.Drop(i) }
func (c *Cluster) Duplicate(i int) bool             { return c.net.Duplicate(i) }

// DeliverIndex delivers in-flight copy i. Delivery to a crashed service is
// lost. ok is false if i is out of range.
func (c *Cluster) DeliverIndex(i int) (ok bool, err error) {
	d, ok := c.net.Deliver(i)
	if !ok {
		return false, nil
	}
	return true, c.dispatch(d)
}

// Next delivers one copy chosen by the seeded schedule; ok is false when the
// wire is empty.
func (c *Cluster) Next() (ok bool, err error) {
	d, ok := c.net.Next()
	if !ok {
		return false, nil
	}
	return true, c.dispatch(d)
}

func (c *Cluster) dispatch(d sim.Delivery[core.Effect]) error {
	if d.Lost {
		return nil
	}
	m := d.Body
	b := Body{O: m.O, A: m.A}
	switch m.Kind {
	case core.WireChargeReq:
		return c.toProv("/charge", b)
	case core.WireRefundReq:
		return c.toProv("/refund", b)
	case core.WireApproved:
		return c.toOrder("/approved", b)
	case core.WireDeclined:
		return c.toOrder("/declined", b)
	}
	return fmt.Errorf("payment: not a wire effect: %v", m.Kind)
}

// Crash takes svc down (if the crash budget allows) and closes its SQLite
// handle. Restart reopens the file; durable rows, outbox included, survive.
func (c *Cluster) Crash(s core.Service) bool {
	if !c.cr.Crash(s.String()) {
		return false
	}
	c.downed(s.String())
	return true
}

func (c *Cluster) Restart(s core.Service) error {
	if c.cr.Up(s.String()) {
		c.cr.Restart(s.String()) // traced as restart-noop
		return nil
	}
	if err := c.svc(s).open(); err != nil { // state unchanged: still down
		return err
	}
	c.cr.Restart(s.String())
	c.log = append(c.log, core.Event{Kind: core.Restart, Svc: s})
	return nil
}

// Snapshot reads both DB files back into a core.State. A crashed service's
// file is read through a temporary handle.
func (c *Cluster) Snapshot() (core.State, error) {
	s := core.Init(c.N)
	s.OrderUp, s.ProvUp = c.cr.Up(core.OrderSvc.String()), c.cr.Up(core.Provider.String())
	for o := uint32(0); o < c.N; o++ {
		os, err := c.order.load(o)
		if err != nil {
			return s, err
		}
		ps, err := c.prov.load(o)
		if err != nil {
			return s, err
		}
		s.Slots[o] = core.Slot{Ord: os.Ord, Prov: ps.Prov}
	}
	return s, nil
}

// Ledger is the provider's Charge/Refund rows in insertion order.
func (c *Cluster) Ledger() ([]core.Effect, error) { return c.prov.Ledger() }
