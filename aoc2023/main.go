package main

import (
	"aoc2023/common"
	"aoc2023/day01"
	"context"
	"fmt"
	"os"
	"os/signal"
	"syscall"
	"time"

	"golang.org/x/sync/errgroup"
)

type waiter interface {
	Wait() error
}

func withTermSignalMonitor(ctx context.Context) (
	context.Context,
	common.GroupFn,
) {
	ctx, cancel := context.WithCancel(ctx)

	fn := func() error {
		sigs := make(chan os.Signal, 1)
		defer close(sigs)

		signal.Notify(sigs, syscall.SIGINT, syscall.SIGTERM)
		defer signal.Stop(sigs)

		select {
		case sig := <-sigs:
			cancel()
			fmt.Println("\n\t*** received termination signal:", sig, "***")
		case <-ctx.Done():
		}

		return nil
	}
	return ctx, fn
}

func waitWithTimeout(
	ctx context.Context,
	w waiter,
	timeout time.Duration,
) error {
	waitResult := make(chan error)
	go func() {
		defer close(waitResult)
		waitResult <- w.Wait()
	}()

	select {
	case err := <-waitResult:
		return err
	case <-ctx.Done():
	}

	graceTimer := time.After(1 * time.Second)
	forcedShutdownTimer := time.After(timeout)

	select {
	case err := <-waitResult:
		return err
	case <-graceTimer:
		fmt.Println("\t*** attempting graceful shutdown")
	case <-forcedShutdownTimer:
		return fmt.Errorf("forced shutdown after %v", timeout)
	}

	select {
	case err := <-waitResult:
		return err
	case <-forcedShutdownTimer:
		return fmt.Errorf("forced shutdown after %v", timeout)
	}
}

func main() {
	ctx, done := context.WithCancel(context.Background())
	ctx, termMonitorFn := withTermSignalMonitor(ctx)
	g, ctx := errgroup.WithContext(ctx)

	g.Go(termMonitorFn)
	firstResult := make(chan string)
	g.Go(func() error {
		defer close(firstResult)
		result, err := day01.SolveA(ctx)
		if err != nil {
			return err
		}
		firstResult <- fmt.Sprintf("%#v", result)
		return nil
	})
	secondResult := make(chan string)
	g.Go(func() error {
		defer close(secondResult)
		result, err := day01.SolveB(ctx)
		if err != nil {
			return err
		}
		secondResult <- fmt.Sprintf("%#v", result)
		return nil
	})
	g.Go(func() error {
		defer done()
		fmt.Println("solution A:", <-firstResult)
		fmt.Println("solution B:", <-secondResult)
		return nil
	})

	if err := waitWithTimeout(ctx, g, 2*time.Second); err != nil {
		fmt.Printf("!!! error: %v\n", err)
	}
}
