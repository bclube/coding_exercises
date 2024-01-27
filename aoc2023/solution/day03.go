package solution

import (
	"aoc2023/common"
	"context"
	"runtime"

	"golang.org/x/sync/errgroup"
)

func SolveDay03(ctx context.Context) (int, error) {
	g, ctx := errgroup.WithContext(ctx)
	g.SetLimit(runtime.NumCPU())

	lines, err := common.ReadAllLines(ctx, "day03.txt")
	if err != nil {
		return 0, err
	}

	var sumOfGearRatios int
	for row, line := range lines {
		for col, c := range line {
			if c == '*' {
				sumOfGearRatios += determineGearRatio(lines, row, col)
			}
		}
	}

	return sumOfGearRatios, g.Wait()
}

func determineGearRatio(lines []string, row, col int) int {
	var first int
	for i := row - 1; i <= row+1; i++ {
		line := lines[i]
		for j := col - 1; j <= col+1; j++ {
			if i == row && j == col {
				continue
			}
			if partNumber := parsePartNumber(line, &j); partNumber != 0 {
				if first != 0 {
					return first * partNumber
				}
				first = partNumber
			}
		}
	}
	return 0
}

func isDigit(c byte) bool {
	return c >= '0' && c <= '9'
}

func parsePartNumber(line string, col *int) int {
	var result int

	factor := 1
	for i := *col; i >= 0; i-- {
		c := line[i]
		if !isDigit(c) {
			break
		}
		result += int(c-'0') * factor
		factor *= 10
	}
	if result == 0 {
		return 0
	}
	for *col++; *col < len(line); *col++ {
		c := line[*col]
		if !isDigit(c) {
			return result
		}
		result = result*10 + int(c-'0')
	}
	return result
}
