package health

import (
	"net/http"

	"github.com/go-chi/chi"
)

func RegisterHandler(mux *chi.Mux) {
	mux.Get("/v1/health", healthHandler)
}

func healthHandler(w http.ResponseWriter, req *http.Request) {
	w.Write([]byte("OK\n"))
}
