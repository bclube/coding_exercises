package solution_test

import (
	"aoc2023/solution"
	"context"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestFindMinimalPath(t *testing.T) {
	want := 94
	got, err := solution.FindMinimalPath(context.Background(),
		[]string{
			"2413432311323",
			"3215453535623",
			"3255245654254",
			"3446585845452",
			"4546657867536",
			"1438598798454",
			"4457876987766",
			"3637877979653",
			"4654967986887",
			"4564679986453",
			"1224686865563",
			"2546548887735",
			"4322674655533",
		})
	require.NoError(t, err)
	require.Equal(t, want, got)
}
