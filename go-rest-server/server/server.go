package server

import (
	"context"
	"fmt"
	"net/http"
	"time"

	"github.com/pkg/errors"
	"go.uber.org/zap"
)

type Server struct {
	logger *zap.Logger
	server *http.Server

	serverStopped chan struct{}
}

func New(logger *zap.Logger, port int, handler http.Handler) *Server {
	stdLog, err := zap.NewStdLogAt(logger, zap.ErrorLevel)
	if err != nil {
		panic(err) // should not happen
	}

	srv := &http.Server{
		Addr:         fmt.Sprintf(":%d", port),
		Handler:      handler,
		ReadTimeout:  10 * time.Second,
		WriteTimeout: 10 * time.Second,
		ErrorLog:     stdLog,
	}

	return &Server{
		logger:        logger,
		server:        srv,
		serverStopped: make(chan struct{}),
	}
}

func (s *Server) Serve() error {
	s.logger.Info("Server start", zap.String("addr", s.server.Addr))

	if err := s.server.ListenAndServe(); err != http.ErrServerClosed {
		return errors.Wrapf(err, "failed to listen and serve")
	}

	<-s.serverStopped
	return nil
}

func (s *Server) Shutdown(ctx context.Context) {
	s.logger.Info("Start graceful shutdown...")

	defer close(s.serverStopped)
	if err := s.server.Shutdown(ctx); err != nil {
		s.logger.Error("Failed to shutdown server", zap.Error(err))
		return
	}

	s.logger.Info("Server stopped")
}
