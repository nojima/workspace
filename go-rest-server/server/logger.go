package server

import (
	"net/http"
	"time"

	"github.com/go-chi/chi/middleware"
	"go.uber.org/zap"
)

func RequestLogger(logger *zap.Logger) func(next http.Handler) http.Handler {
	return func(next http.Handler) http.Handler {
		return requestLogger(next, logger)
	}
}

func requestLogger(next http.Handler, logger *zap.Logger) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, req *http.Request) {
		writer := middleware.NewWrapResponseWriter(w, req.ProtoMajor)
		startAt := time.Now()

		next.ServeHTTP(writer, req)

		endAt := time.Now()
		logger.Info(
			"Access",
			zap.String("method", req.Method),
			zap.String("url", req.URL.String()),
			zap.Int("status", writer.Status()),
			zap.Int("response_size", writer.BytesWritten()),
			zap.Duration("elapsed", endAt.Sub(startAt)),
		)
	})
}
