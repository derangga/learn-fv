package inventory

import (
	"encoding/json"
	"errors"
	"fmt"
	"log"
	"net"
	"net/http"
	"time"

	"github.com/go-chi/chi/v5"

	"github.com/derangga/learn-formal-verification/internal/uc2/core"
)

// body is the JSON request body; unused fields are ignored.
type body struct {
	ID  int64 `json:"id"`
	Sku int64 `json:"sku"`
	Qty int64 `json:"qty"`
	Ttl int64 `json:"ttl"`
}

// Handler serves POST /reserve /confirm /expire /tick. 200 returns the
// effects as JSON, 503 when crashed, 400 on bad JSON.
func (s *Service) Handler() http.Handler {
	r := chi.NewRouter()
	for k, p := range paths {
		r.Post(p, func(w http.ResponseWriter, r *http.Request) {
			var b body
			if err := json.NewDecoder(r.Body).Decode(&b); err != nil {
				http.Error(w, err.Error(), http.StatusBadRequest)
				return
			}
			fx, err := s.apply(core.Event{Kind: k, ID: b.ID, Sku: b.Sku, Qty: b.Qty, Ttl: b.Ttl})
			switch {
			case errors.Is(err, ErrDown):
				http.Error(w, err.Error(), http.StatusServiceUnavailable)
			case err != nil:
				http.Error(w, err.Error(), http.StatusInternalServerError)
			default:
				out, _ := json.Marshal(fx)
				w.Write(out)
			}
		})
	}
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
		return nil, nil, fmt.Errorf("inventory: %q is not 127.0.0.1", addr)
	}
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return nil, nil, err
	}
	srv := &http.Server{Handler: h, ReadHeaderTimeout: 5 * time.Second}
	go func() {
		if err := srv.Serve(l); err != nil && !errors.Is(err, http.ErrServerClosed) {
			log.Printf("inventory: serve %s: %v", l.Addr(), err)
		}
	}()
	return l.Addr(), func() { srv.Close() }, nil
}
