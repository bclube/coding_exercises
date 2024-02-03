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
