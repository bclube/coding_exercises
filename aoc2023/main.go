package main

import (
	"context"
	"fmt"
	"os"
	"os/signal"
	"sync"
	"syscall"
	"time"
)

func setupSignalHandler(ctx context.Context, cancel context.CancelFunc, wg *sync.WaitGroup) {
	sigs := make(chan os.Signal, 1)
	signal.Notify(sigs, syscall.SIGINT, syscall.SIGTERM)

	wg.Add(1)
	go func() {
		defer wg.Done()
		select {
		case <-sigs:
			cancel()
		case <-ctx.Done():
		}
	}()
}

func waitWithTimeout(wg *sync.WaitGroup, timeout time.Duration) {
	done := make(chan struct{})
	go func() {
		defer close(done)
		wg.Wait()
	}()

	select {
	case <-done:
	case <-time.After(timeout):
		fmt.Printf("!!! forced shutdown after %v\n", timeout)
	}
}

func main() {
	var wg sync.WaitGroup
	ctx, cancel := context.WithCancel(context.Background())
	defer func() {
		cancel()
		waitWithTimeout(&wg, 5*time.Second)
	}()

	setupSignalHandler(ctx, cancel, &wg)

	fmt.Println("Hello, world")
}
