package payment

import (
	"encoding/json"
	"errors"
	"fmt"
	"log"
	"math/rand/v2"
	"net"
	"net/http"
	"time"

	"github.com/go-chi/chi/v5"

	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

type rngSrc = rand.Rand

// NewSeededIssuer declines each first request with probability p.
func NewSeededIssuer(seed uint64, p float64) *SeededIssuer {
	return &SeededIssuer{P: p, rng: rand.New(rand.NewPCG(seed, 0x155))}
}

func (s *SeededIssuer) Decide(uint32) core.Decision {
	if s.rng.Float64() < s.P {
		return core.Decline
	}
	return core.Approve
}

// Body is the JSON request body: order id and (where used) amount.
type Body struct {
	O uint32 `json:"o"`
	A uint32 `json:"a"`
}

type applyFn func(core.Event) ([]core.Effect, error)

// route builds the POST handler for one event kind. decide, if set, fills D.
func route(k core.Kind, apply applyFn, up func() bool, decide func(o uint32) core.Decision) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var b Body
		if err := json.NewDecoder(r.Body).Decode(&b); err != nil {
			http.Error(w, err.Error(), http.StatusBadRequest)
			return
		}
		e := core.Event{Kind: k, O: b.O, A: b.A}
		if decide != nil && up() { // do not draw an answer for a down service
			e.D = decide(b.O)
		}
		fx, err := apply(e)
		switch {
		case errors.Is(err, ErrDown):
			http.Error(w, err.Error(), http.StatusServiceUnavailable)
		case err != nil:
			http.Error(w, err.Error(), http.StatusInternalServerError)
		default:
			out, merr := json.Marshal(fx)
			if merr != nil {
				http.Error(w, merr.Error(), http.StatusInternalServerError)
				return
			}
			w.Write(out)
		}
	}
}

func (s *OrderSvc) up() bool { return s.db != nil && s.cr.Up(s.name) }
func (s *ProvSvc) up() bool  { return s.db != nil && s.cr.Up(s.name) }

// Handler serves the order endpoints: client events and delivered replies.
func (s *OrderSvc) Handler() http.Handler {
	r := chi.NewRouter()
	for p, k := range map[string]core.Kind{
		"/place": core.PlaceOrder, "/retry": core.RetryTimeout, "/refund": core.RefundOrder,
		"/flush/charge": core.FlushChargeReq, "/flush/refund": core.FlushRefundReq,
		"/approved": core.PaymentApproved, "/declined": core.PaymentDeclined,
	} {
		r.Post(p, route(k, s.Apply, s.up, nil))
	}
	return r
}

// Handler serves the provider endpoints: delivered requests and the reply flush.
func (s *ProvSvc) Handler() http.Handler {
	r := chi.NewRouter()
	r.Post("/charge", route(core.ChargeReqRecv, s.Apply, s.up, s.issuer.Decide))
	r.Post("/refund", route(core.RefundReqRecv, s.Apply, s.up, nil))
	r.Post("/flush/reply", route(core.FlushReply, s.Apply, s.up, nil))
	return r
}

// ListenLocal serves h on a loopback address (use "127.0.0.1:0" for any port).
// Any non-loopback host is refused.
func ListenLocal(h http.Handler, addr string) (net.Addr, func(), error) {
	host, _, err := net.SplitHostPort(addr)
	if err != nil {
		return nil, nil, err
	}
	if host != "127.0.0.1" {
		return nil, nil, fmt.Errorf("payment: %q is not 127.0.0.1", addr)
	}
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return nil, nil, err
	}
	srv := &http.Server{Handler: h, ReadHeaderTimeout: 5 * time.Second}
	go func() {
		if err := srv.Serve(l); err != nil && !errors.Is(err, http.ErrServerClosed) {
			log.Printf("payment: serve %s: %v", l.Addr(), err)
		}
	}()
	return l.Addr(), func() { srv.Close() }, nil
}
