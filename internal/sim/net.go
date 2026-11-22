package sim

import (
	"fmt"
	"math/rand/v2"
)

// Faults configures the random mode of Net.Next. Zero value: perfectly
// reliable and FIFO (oldest in-flight message first).
type Faults struct {
	Drop    float64 // chance one in-flight copy is dropped per fault roll
	Dup     float64 // chance one in-flight copy is duplicated per fault roll
	MaxDup  int     // max duplicates per original message (TLA+ DupMax)
	Reorder bool    // pick the delivered message at random instead of FIFO
}

// Msg is one in-flight copy. Orig is the id of the original Send.
type Msg[M any] struct {
	ID, Orig int
	To       string
	Body     M
}

// Delivery is what the driver hands to a service. Lost means the destination
// was down: the copy is consumed with no effect.
type Delivery[M any] struct {
	To   string
	Body M
	Lost bool
}

// Net is a single-threaded bag of in-flight messages. Order is not preserved
// in scripted mode, and in random mode when Faults.Reorder is set. Send does
// not check the sender: services guard their own sends while down.
type Net[M any] struct {
	f      Faults
	rng    *rand.Rand
	cr     *Crasher // may be nil: all services up
	trace  *Trace
	flight []Msg[M]
	nextID int
	dups   map[int]int
}

func NewNet[M any](seed uint64, f Faults, cr *Crasher, trace *Trace) *Net[M] {
	return &Net[M]{f: f, rng: rand.New(rand.NewPCG(seed, 0x4e37)), cr: cr, trace: trace, dups: map[int]int{}}
}

func (n *Net[M]) Send(to string, m M) {
	id := n.nextID
	n.nextID++
	n.flight = append(n.flight, Msg[M]{ID: id, Orig: id, To: to, Body: m})
	n.trace.add("send", to, fmt.Sprintf("id=%d", id))
}

// InFlight lists the copies currently on the wire (a copy of the bag).
func (n *Net[M]) InFlight() []Msg[M] { return append([]Msg[M](nil), n.flight...) }

// Next advances the random schedule. It rolls faults (drop, duplicate) until
// none fires, then delivers one copy, and returns false when nothing is in
// flight. A dropped message is not delivered, so Next keeps going.
func (n *Net[M]) Next() (Delivery[M], bool) {
	for len(n.flight) > 0 {
		r := n.rng.Float64()
		switch {
		case r < n.f.Drop:
			n.Drop(n.rng.IntN(len(n.flight)))
		case r < n.f.Drop+n.f.Dup:
			i := n.rng.IntN(len(n.flight))
			if !n.Duplicate(i) { // bound hit (traced): fall through to a delivery
				d, _ := n.Deliver(n.pick())
				return d, true
			}
		default:
			d, _ := n.Deliver(n.pick())
			return d, true
		}
	}
	return Delivery[M]{}, false
}

func (n *Net[M]) pick() int {
	if n.f.Reorder {
		return n.rng.IntN(len(n.flight))
	}
	return 0
}

// Deliver removes copy i and hands it out; Lost is set if the destination is
// down. ok is false (nothing traced) if i is out of range.
func (n *Net[M]) Deliver(i int) (d Delivery[M], ok bool) {
	if !n.valid(i) {
		return d, false
	}
	m := n.take(i)
	lost := n.cr != nil && !n.cr.Up(m.To)
	kind := "deliver"
	if lost {
		kind = "lost"
	}
	n.trace.add(kind, m.To, fmt.Sprintf("id=%d orig=%d", m.ID, m.Orig))
	return Delivery[M]{To: m.To, Body: m.Body, Lost: lost}, true
}

// Drop discards copy i. It returns false (nothing traced) if i is out of range.
func (n *Net[M]) Drop(i int) bool {
	if !n.valid(i) {
		return false
	}
	m := n.take(i)
	n.trace.add("drop", m.To, fmt.Sprintf("id=%d orig=%d", m.ID, m.Orig))
	return true
}

func (n *Net[M]) valid(i int) bool { return i >= 0 && i < len(n.flight) }

// Duplicate adds a copy of copy i, unless the original already has MaxDup
// duplicates (traced as dup-denied). It reports whether a copy was added; an
// out-of-range i also returns false and traces nothing.
func (n *Net[M]) Duplicate(i int) bool {
	if !n.valid(i) {
		return false
	}
	m := n.flight[i]
	if n.dups[m.Orig] >= n.f.MaxDup {
		n.trace.add("dup-denied", m.To, fmt.Sprintf("orig=%d of=%d", m.Orig, m.ID))
		return false
	}
	n.dups[m.Orig]++
	id := n.nextID
	n.nextID++
	n.flight = append(n.flight, Msg[M]{ID: id, Orig: m.Orig, To: m.To, Body: m.Body})
	n.trace.add("dup", m.To, fmt.Sprintf("id=%d orig=%d of=%d", id, m.Orig, m.ID))
	return true
}

func (n *Net[M]) take(i int) Msg[M] {
	m := n.flight[i]
	n.flight = append(n.flight[:i:i], n.flight[i+1:]...)
	return m
}
