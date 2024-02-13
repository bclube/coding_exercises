package solution

import (
	"aoc2023/common"
	"context"

	"golang.org/x/sync/errgroup"
)

// TODO: Improve readability of the code
func SolveDay13(ctx context.Context) (int, error) {
	g, ctx := errgroup.WithContext(ctx)
	lines, lineReader := common.LinesFromFile(ctx, "day13.txt")
	g.Go(lineReader)
	grids, gridReader := common.Scan(ctx, lines, make([]string, 0, 17),
		func(ctx context.Context, acc []string, line string) ([]string, []string, bool, error) {
			if len(line) == 0 {
				return make([]string, 0, 17), acc, true, nil
			}
			return append(acc, line), nil, false, nil
		},
		func(ctx context.Context, acc []string) ([]string, bool, error) {
			return acc, true, nil
		})
	g.Go(gridReader)
	var sum int
	g.Go(common.ForEach(ctx, grids, func(ctx context.Context, grid []string) error {
		rowSymmetry := locateRowSymmetry(grid, 1)
		if rowSymmetry != 0 {
			sum += 100 * rowSymmetry
			return nil
		}
		sum += locateColumnSymmetry(grid, 1)
		return nil
	}))

	return sum, g.Wait()
}

func locateRowSymmetry(grid []string, smudgeCount int) int {
outerLoop:
	for i := 0; i < len(grid)-1; i++ {
		remainingSmudges := smudgeCount
		for j := 0; j < len(grid); j++ {
			ti := i - j
			bi := i + j + 1
			if ti < 0 || bi >= len(grid) {
				if remainingSmudges == 0 {
					return i + 1
				}
				continue outerLoop
			}
			upperRow := grid[ti]
			lowerRow := grid[bi]
			for k := range upperRow {
				if upperRow[k] != lowerRow[k] {
					if remainingSmudges == 0 {
						continue outerLoop
					}
					remainingSmudges--
				}
			}
		}
	}
	return 0
}

func locateColumnSymmetry(grid []string, smudgeCount int) int {
	symmetries := make(map[int]int, len(grid[0]))
	for i := 0; i < len(grid[0])-1; i++ {
		symmetries[i] = smudgeCount
	}
	for _, row := range grid {
	nextColumn:
		for i, remainingSmudges := range symmetries {
			if remainingSmudges < 0 {
				continue
			}
			for j := 0; j < len(row); j++ {
				li := i - j
				ri := i + j + 1
				if li < 0 || ri >= len(row) {
					continue nextColumn
				}
				if row[li] != row[ri] {
					symmetries[i]--
					remainingSmudges--
					if remainingSmudges < 0 {
						continue nextColumn
					}
				}
			}
		}
	}
	foundOne := false
	var result int
	for i, remainingSmudges := range symmetries {
		if remainingSmudges != 0 {
			continue
		}
		if foundOne {
			panic("found more than one symmetry in the grid")
		}
		foundOne = true
		result = i
	}
	if !foundOne {
		panic("could not find a unique symmetry in the grid")
	}
	return result + 1
}
