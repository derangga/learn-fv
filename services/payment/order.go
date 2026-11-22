package payment

import (
	"database/sql"

	"github.com/derangga/learn-formal-verification/internal/sim"
	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

const orderSchema = `
CREATE TABLE IF NOT EXISTS ord(o INTEGER PRIMARY KEY, status INTEGER NOT NULL, amount INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS outbox(o INTEGER NOT NULL, kind TEXT NOT NULL, PRIMARY KEY(o, kind));`

// OrderSvc owns orders and the charge/refund outbox.
type OrderSvc struct{ base }

func newOrderSvc(path string, n uint32, cr *sim.Crasher) *OrderSvc {
	return &OrderSvc{base{name: core.OrderSvc.String(), path: path, schema: orderSchema, n: n, cr: cr}}
}

// Apply runs one order-side event (client events, Flush*, Approved, Declined).
func (s *OrderSvc) Apply(e core.Event) ([]core.Effect, error) {
	return s.apply(e, loadOrd, saveOrd)
}

func loadOrd(q querier, o uint32) (core.Slot, error) {
	var sl core.Slot
	var st uint32
	if err := scanOrNone(q.QueryRow(`SELECT status, amount FROM ord WHERE o=?`, o), &st, &sl.Ord.Amount); err != nil {
		return sl, err
	}
	sl.Ord.Status = core.Status(st)
	var err error
	if sl.Ord.OutCharge, err = hasRow(q, o, "charge"); err != nil {
		return sl, err
	}
	sl.Ord.OutRefund, err = hasRow(q, o, "refund")
	return sl, err
}

func saveOrd(tx *sql.Tx, o uint32, sl core.Slot, _ []core.Effect) error {
	d := sl.Ord
	if _, err := tx.Exec(`INSERT INTO ord(o, status, amount) VALUES(?,?,?)
		ON CONFLICT(o) DO UPDATE SET status=excluded.status, amount=excluded.amount`, o, d.Status, d.Amount); err != nil {
		return err
	}
	if err := setRow(tx, o, "charge", d.OutCharge); err != nil {
		return err
	}
	return setRow(tx, o, "refund", d.OutRefund)
}

// load reads the durable order half of slot o (works while crashed).
func (s *OrderSvc) load(o uint32) (sl core.Slot, err error) {
	err = s.read(func(q querier) (e error) { sl, e = loadOrd(q, o); return })
	return
}
