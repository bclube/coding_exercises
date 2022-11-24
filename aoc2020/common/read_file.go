package common

import (
	"bufio"
	"os"
)

func ParseFile[T any](path string, parse_line_f func(string) (T, error)) (<-chan T, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	out := make(chan T)
	go func() {
		defer file.Close()
		defer close(out)
		scanner := bufio.NewScanner(file)
		for scanner.Scan() {
			parsed, err := parse_line_f(scanner.Text())
			if err != nil {
				panic(err)
			}
			out <- parsed
		}
	}()
	return out, nil
}
