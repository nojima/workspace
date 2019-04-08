package main

import (
	"context"
	"log"
	"os"
	"os/signal"
	"syscall"
	"time"

	"github.com/go-chi/chi"
	"github.com/nojima/workspace/go-rest-server/health"
	"github.com/nojima/workspace/go-rest-server/server"
	"go.uber.org/zap"
)

func main() {
	logger, err := zap.NewDevelopment()
	if err != nil {
		log.Fatalf("Failed to setup logger: %v", err)
	}

	if err := doMain(logger); err != nil {
		logger.Fatal("An error has occurred", zap.Error(err))
	}
}

func doMain(logger *zap.Logger) error {
	mux := chi.NewRouter()
	mux.Use(server.RequestLogger(logger))

	health.RegisterHandler(mux)

	ctx := context.Background()
	srv := server.New(logger, 8080, mux)

	go handleSIGTERM(ctx, srv)

	return srv.Serve()
}

func handleSIGTERM(ctx context.Context, srv *server.Server) {
	sigterm := make(chan os.Signal, 1)
	signal.Notify(sigterm, syscall.SIGTERM)
	<-sigterm

	shutdownTimeout := 10 * time.Second
	shutdownContext, cancel := context.WithTimeout(ctx, shutdownTimeout)
	defer cancel()

	srv.Shutdown(shutdownContext)
}
