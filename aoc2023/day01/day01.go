package day01

import (
	"aoc2023/common"
	"context"
	"fmt"
	"math"
	"regexp"

	"golang.org/x/sync/errgroup"
)

func solve(ctx context.Context, extractFn func(context.Context, string) (int, error)) (int, error) {
	g, ctx := errgroup.WithContext(ctx)

	lines, readFn := common.LinesFromFile(ctx, "day01/input.txt")
	g.Go(readFn)
	calibrationValues, mapFn := common.MapValues(ctx, lines, extractFn)
	g.Go(mapFn)
	var sum int
	g.Go(common.ForEach(ctx, calibrationValues, func(_ context.Context, v int) error {
		sum += v
		return nil
	}))

	return sum, g.Wait()
}

func SolveA(ctx context.Context) (int, error) {
	return solve(ctx, ExtractCalibrationValue)
}

func SolveB(ctx context.Context) (int, error) {
	return solve(ctx, ExtractCalibrationValueV2)
}

func ExtractCalibrationValue(_ context.Context, line string) (int, error) {
	return extractCalibrationValue(line, calibrationValueExtractorV1)
}

func ExtractCalibrationValueV2(_ context.Context, line string) (int, error) {
	return extractCalibrationValue(line, calibrationValueExtractorV2)
}

func extractCalibrationValue(line string, extractor map[*regexp.Regexp]func(byte) int) (int, error) {
	var first, last int
	firstIndex := math.MaxInt
	lastIndex := math.MinInt
	for regex, convertFn := range extractor {
		matches := regex.FindAllStringIndex(line, -1)

		if len(matches) == 0 {
			continue
		}

		if firstMatch := matches[0]; firstMatch[0] < firstIndex {
			first = convertFn(line[firstMatch[0]])
			firstIndex = firstMatch[0]
		}
		if lastMatch := matches[len(matches)-1]; lastMatch[1] > lastIndex {
			last = convertFn(line[lastMatch[0]])
			lastIndex = lastMatch[1]
		}
	}
	if firstIndex == math.MaxInt || lastIndex == math.MinInt {
		return 0, fmt.Errorf("no digits found in %q", line)
	}
	return first*10 + last, nil
}

var calibrationValueExtractorV1 = map[*regexp.Regexp]func(byte) int{
	regexp.MustCompile(`\d`): func(match byte) int { return int(match - '0') },
}
var calibrationValueExtractorV2 = func() map[*regexp.Regexp]func(byte) int {
	v2 := map[*regexp.Regexp]func(byte) int{
		regexp.MustCompile(`one`):   func(byte) int { return 1 },
		regexp.MustCompile(`two`):   func(byte) int { return 2 },
		regexp.MustCompile(`three`): func(byte) int { return 3 },
		regexp.MustCompile(`four`):  func(byte) int { return 4 },
		regexp.MustCompile(`five`):  func(byte) int { return 5 },
		regexp.MustCompile(`six`):   func(byte) int { return 6 },
		regexp.MustCompile(`seven`): func(byte) int { return 7 },
		regexp.MustCompile(`eight`): func(byte) int { return 8 },
		regexp.MustCompile(`nine`):  func(byte) int { return 9 },
		regexp.MustCompile(`zero`):  func(byte) int { return 0 },
	}
	for k, v := range calibrationValueExtractorV1 {
		v2[k] = v
	}
	return v2
}()
