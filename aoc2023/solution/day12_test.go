package solution_test

import (
	"aoc2023/solution"
	"context"
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestCountValidPermutations(t *testing.T) {
	testCases := []struct {
		input string
		want  int
	}{
		{"???.### 1,1,3", 1},
		{".??..??...?##. 1,1,3", 16384},
		{"?#?#?#?#?#?#?#? 1,3,1,6", 1},
		{"????.#...#... 4,1,1", 16},
		{"????.######..#####. 1,6,5", 2500},
		{"?###???????? 3,2,1", 506250},
	}
	for _, tC := range testCases {
		t.Run(tC.input, func(t *testing.T) {
			fmt.Println("input:", tC.input)
			got, err := solution.CountValidArrangements(context.Background(), tC.input)
			require.NoError(t, err)
			require.Equal(t, tC.want, got)
		})
	}
}
