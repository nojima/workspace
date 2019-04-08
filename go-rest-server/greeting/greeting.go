package greeting

import (
	"fmt"
	"net/http"

	"github.com/go-chi/chi"
)

func RegisterHandler(mux *chi.Mux) {
	mux.Get("/v1/greeting/{name}", greetingHandler)
}

func greetingHandler(w http.ResponseWriter, req *http.Request) {
	name := chi.URLParam(req, "name")
	fmt.Fprintf(w, "Hi, %v!", name)
}
