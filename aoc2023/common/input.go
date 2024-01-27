package common

import (
	"bufio"
	"context"
	"os"
	"path/filepath"
	"strings"

	"github.com/pkg/errors"
)

func ReadAllLines(ctx context.Context, fileName string) ([]string, error) {
	file, err := os.Open(filePath(fileName))
	if err != nil {
		return nil, errors.WithStack(err)
	}
	defer file.Close()
	scanner := bufio.NewScanner(file)
	result := make([]string, 0, 200)
	for scanner.Scan() {
		select {
		case <-ctx.Done():
			return nil, ctx.Err()
		default:
		}
		result = append(result, scanner.Text())
	}

	return result, scanner.Err()
}

func filePath(fileName string) string {
	return filepath.Join("/workspaces/coding_exercises/aoc2023/input", fileName)
}

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
		path := filePath(fileName)
		file, err := os.Open(path)
		if err != nil {
			return errors.WithStack(err)
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
