package solution_test

import (
	"aoc2023/common"
	"aoc2023/solution"
	"context"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestSolveDay03(t *testing.T) {
	ctx := context.Background()
	lines, readFn := common.LinesFromString(ctx, `
	467..114..
	...*......
	..35..633.
	......#...
	617*......
	.....+.58.
	..592.....
	......755.
	...$.*....
	.664.598..
	`)

	go readFn()

	want := 467835
	got, err := solution.GetPartNumbers(ctx, lines)
	require.NoError(t, err)
	require.Equal(t, want, got)
}
