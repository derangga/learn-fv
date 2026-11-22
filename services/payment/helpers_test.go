package payment

import (
	"net/http"
	"net/http/httptest"
	"strings"
)

func newRec() *httptest.ResponseRecorder { return httptest.NewRecorder() }
func newReq(path, body string) *http.Request {
	return httptest.NewRequest(http.MethodPost, path, strings.NewReader(body))
}
