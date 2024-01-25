package common

import (
	"bufio"
	"context"
	"os"
	"path/filepath"
	"strings"
)

func LinesFromString(ctx context.Context, text string) (<-chan string, GroupFn) {
	out := make(chan string, 1)

	fn := func() (err error) {
		defer close(out)
		reader := strings.NewReader(text)
		scanner := bufio.NewScanner(reader)

		for scanner.Scan() {
			select {
			case <-ctx.Done():
				return ctx.Err()
			case out <- scanner.Text():
			}
		}

		return scanner.Err()
	}

	return out, fn
}

func LinesFromFile(ctx context.Context, fileName string) (
	<-chan string,
	GroupFn,
) {
	out := make(chan string, 1)

	fn := func() (e error) {
		defer close(out)
		path := filepath.Join("/workspaces/coding_exercises/aoc2023", fileName)
		file, err := os.Open(path)
		if err != nil {
			return err
		}
		defer func() {
			err := file.Close()
			if e == nil {
				e = err
			}
		}()

		scanner := bufio.NewScanner(file)

		for scanner.Scan() {
			select {
			case <-ctx.Done():
				return ctx.Err()
			case out <- scanner.Text():
			}
		}

		return scanner.Err()
	}

	return out, fn
}
