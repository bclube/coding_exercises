package solution_test

import (
	"aoc2023/solution"
	"testing"

	"github.com/stretchr/testify/require"
)

func Test(t *testing.T) {
	testCases := []struct {
		in   string
		want byte
	}{
		{"H", 200},
		{"HA", 153},
		{"HAS", 172},
		{"HASH", 52},
		{"rn=1", 30},
		{"cm-", 253},
		{"qp=3", 97},
		{"cm=2", 47},
		{"qp-", 14},
		{"pc=4", 180},
		{"ot=9", 9},
		{"ab=5", 197},
		{"pc-", 48},
		{"pc=6", 214},
		{"ot=7", 231},
	}
	for _, tC := range testCases {
		t.Run(tC.in, func(t *testing.T) {
			got := solution.ComputeHash(tC.in)
			require.Equal(t, tC.want, got)
		})
	}
}
