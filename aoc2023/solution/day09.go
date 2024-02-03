package solution

import (
	"aoc2023/common"
	"context"
	"strconv"
	"strings"

	"golang.org/x/sync/errgroup"
)

func SolveDay09(ctx context.Context) (int, error) {
	g, ctx := errgroup.WithContext(ctx)
	lines, lineReader := common.LinesFromFile(ctx, "day09.txt")
	g.Go(lineReader)
	histories, mappingFn := common.MapValues(ctx, lines, parseEcoHistory)
	g.Go(mappingFn)
	var sum int
	g.Go(common.ForEach(ctx, histories, func(ctx context.Context, h []int) error {
		sum += extrapolateNextValue(ctx, h)
		return nil
	}))
	return sum, g.Wait()
}

func extrapolateNextValue(ctx context.Context, history []int) int {
	if historyContainsAllZeroes(history) {
		return 0
	}
	diffs := make([]int, len(history)-1)
	for i := 1; i < len(history); i++ {
		diffs[i-1] = history[i] - history[i-1]
	}
	return history[0] - extrapolateNextValue(ctx, diffs)
}

func historyContainsAllZeroes(history []int) bool {
	for _, value := range history {
		if value != 0 {
			return false
		}
	}
	return true
}

func parseEcoHistory(ctx context.Context, line string) ([]int, error) {
	segments := strings.Split(line, " ")
	results := make([]int, len(segments))
	for i, segment := range segments {
		results[i], _ = strconv.Atoi(segment)
	}
	return results, nil
}
