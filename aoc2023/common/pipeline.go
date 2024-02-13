package common

import (
	"context"
)

func ForEachWithIndex[A any](ctx context.Context, in <-chan A, f func(context.Context, int, A) error) GroupFn {
	return func() error {
		for i := 0; ; i++ {
			select {
			case <-ctx.Done():
				return ctx.Err()
			case v, hasValue := <-in:
				if !hasValue {
					return nil
				}
				if err := f(ctx, i, v); err != nil {
					return err
				}
			}
		}
	}
}

func ForEach[A any](ctx context.Context, in <-chan A, f func(context.Context, A) error) GroupFn {
	return ForEachWithIndex(ctx, in, func(ctx context.Context, _ int, v A) error {
		return f(ctx, v)
	})
}

func Scan[A, B, C any](ctx context.Context, in <-chan A, acc C,
	scanFn func(context.Context, C, A) (C, B, bool, error),
	finally func(context.Context, C) (B, bool, error),
) (
	<-chan B,
	GroupFn,
) {
	out := make(chan B, 1)

	fn := func() error {
		defer close(out)
		var err error
		var result B
		var emitValue bool
	loop:
		for {
			var input A
			select {
			case <-ctx.Done():
				return ctx.Err()
			case v, hasValue := <-in:
				if !hasValue {
					break loop
				}
				input = v
			}
			acc, result, emitValue, err = scanFn(ctx, acc, input)
			if err != nil {
				return err
			}
			if emitValue {
				select {
				case <-ctx.Done():
					return ctx.Err()
				case out <- result:
				}
			}
		}
		if finally != nil {
			result, emitValue, err = finally(ctx, acc)
			if err != nil {
				return err
			}
			if emitValue {
				select {
				case <-ctx.Done():
					return ctx.Err()
				case out <- result:
				}
			}
		}
		return nil
	}

	return out, fn
}

func FlatMap[A, B any](ctx context.Context, in <-chan A, f func(context.Context, A, chan<- B) error) (
	<-chan B,
	GroupFn,
) {
	out := make(chan B, 1)

	fn := func() error {
		defer close(out)
		for {
			var input A
			select {
			case <-ctx.Done():
				return ctx.Err()
			case v, hasValue := <-in:
				if !hasValue {
					return nil
				}
				input = v
			}
			if err := f(ctx, input, out); err != nil {
				return err
			}
		}
	}

	return out, fn
}

func MapValues[A, B any](ctx context.Context, in <-chan A, f func(context.Context, A) (B, error)) (
	<-chan B,
	GroupFn,
) {
	out := make(chan B, 1)

	fn := func() error {
		defer close(out)
		for {
			var input A
			select {
			case <-ctx.Done():
				return ctx.Err()
			case v, hasValue := <-in:
				if !hasValue {
					return nil
				}
				input = v
			}
			result, err := f(ctx, input)
			if err != nil {
				return err
			}
			select {
			case <-ctx.Done():
				return ctx.Err()
			case out <- result:
			}
		}
	}

	return out, fn
}
