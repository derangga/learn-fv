// Package payment is the UC1 system: an order service and a payment provider,
// each with its own SQLite file, talking through outbox rows and HTTP handlers.
// All business logic is core.Step; this package loads a slot, calls Step and
// writes the result back in one transaction.
package payment

import (
	"database/sql"
	"errors"

	_ "modernc.org/sqlite" // pure-Go driver, no cgo

	"github.com/derangga/learn-formal-verification/internal/sim"
	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

// ErrDown is returned for any request to a crashed service.
var ErrDown = errors.New("payment: service down")

type querier interface {
	QueryRow(query string, args ...any) *sql.Row
	Query(query string, args ...any) (*sql.Rows, error)
}

func isWire(k core.EffectKind) bool {
	switch k {
	case core.WireChargeReq, core.WireRefundReq, core.WireApproved, core.WireDeclined:
		return true
	}
	return false
}

func isLedger(k core.EffectKind) bool { return k == core.Charge || k == core.Refund }

type loadFn func(q querier, o uint32) (core.Slot, error)
type saveFn func(tx *sql.Tx, o uint32, sl core.Slot, fx []core.Effect) error

// base is what both services share: a file, a handle that is nil while the
// service is crashed, and the hooks the cluster wires in.
type base struct {
	name, path, schema string
	n                  uint32
	db                 *sql.DB
	cr                 *sim.Crasher
	send               func(core.Effect) // transport: gets Wire* effects after commit
	onApply            func(core.Event)  // log of applied events
}

func (b *base) open() error {
	db, err := openDB(b.path, b.schema)
	if err != nil {
		return err
	}
	b.db = db
	return nil
}

func openDB(path, schema string) (*sql.DB, error) {
	db, err := sql.Open("sqlite", "file:"+path+"?_pragma=synchronous(OFF)&_pragma=busy_timeout(5000)")
	if err != nil {
		return nil, err
	}
	db.SetMaxOpenConns(1)
	if _, err := db.Exec(schema); err != nil {
		db.Close()
		return nil, err
	}
	return db, nil
}

func (b *base) close() {
	if b.db != nil {
		b.db.Close()
		b.db = nil
	}
}

// read runs fn on the live handle, or on a temporary one while crashed
// (Snapshot must read a crashed service's durable file).
func (b *base) read(fn func(q querier) error) error {
	if b.db != nil {
		return fn(b.db)
	}
	db, err := openDB(b.path, b.schema)
	if err != nil {
		return err
	}
	defer db.Close()
	return fn(db)
}

// apply is the whole service logic: tx{load slot; core.Step; save}, then hand
// Wire* effects to the transport. Core's own up flags stay true; a down
// service is refused here, which is the same as Step's rule D.
func (b *base) apply(e core.Event, load loadFn, save saveFn) ([]core.Effect, error) {
	if b.db == nil || !b.cr.Up(b.name) {
		return nil, ErrDown
	}
	s := core.Init(b.n)
	in := e.O < b.n
	tx, err := b.db.Begin()
	if err != nil {
		return nil, err
	}
	defer tx.Rollback()
	if in {
		if s.Slots[e.O], err = load(tx, e.O); err != nil {
			return nil, err
		}
	}
	s2, fx := core.Step(s, e)
	if in {
		if err := save(tx, e.O, s2.Slots[e.O], fx); err != nil {
			return nil, err
		}
	}
	if err := tx.Commit(); err != nil {
		return nil, err
	}
	for _, f := range fx {
		if isWire(f.Kind) {
			b.send(f)
		}
	}
	b.onApply(e)
	return fx, nil
}

// Outbox rows: presence of (o, kind) is the flag.
func hasRow(q querier, o uint32, kind string) (bool, error) {
	var c int
	err := q.QueryRow(`SELECT COUNT(*) FROM outbox WHERE o=? AND kind=?`, o, kind).Scan(&c)
	return c > 0, err
}

func setRow(tx *sql.Tx, o uint32, kind string, on bool) error {
	var err error
	if on {
		_, err = tx.Exec(`INSERT OR IGNORE INTO outbox(o, kind) VALUES(?, ?)`, o, kind)
	} else {
		_, err = tx.Exec(`DELETE FROM outbox WHERE o=? AND kind=?`, o, kind)
	}
	return err
}

func scanOrNone(r *sql.Row, dst ...any) error {
	if err := r.Scan(dst...); err != nil && !errors.Is(err, sql.ErrNoRows) {
		return err
	}
	return nil
}
