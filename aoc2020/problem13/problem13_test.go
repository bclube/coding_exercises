package problem13

import "testing"

func TestSolveA(t *testing.T) {
	tests := []struct {
		in       string
		expected int
	}{
		{in: "../testdata/input13.txt", expected: 295},
	}
	for _, test := range tests {
		got, _, err := SolveBoth(test.in)
		if err != nil {
			t.Errorf(err.Error())
		} else if got != test.expected {
			t.Errorf("SolveBoth<<A>>(%q) == %d; expected %d", test.in, got, test.expected)
		}
	}
}

func TestSolveB(t *testing.T) {
	tests := []struct {
		in       []int
		expected int
	}{
		{in: []int{3, 5}, expected: 9},
		{in: []int{7, 13, -1, -1, 59, -1, 31, 19}, expected: 1068781},
		{in: []int{17, -1, 13, 19}, expected: 3417},
		{in: []int{67, 7, 59, 61}, expected: 754018},
		{in: []int{67, -1, 7, 59, 61}, expected: 779210},
		{in: []int{67, 7, -1, 59, 61}, expected: 1261476},
		{in: []int{1789, 37, 47, 1889}, expected: 1202161486},
	}
	for _, test := range tests {
		got := SolveB(test.in)
		if got != test.expected {
			t.Errorf("SolveBoth<<B>>(%v) == %d; expected %d", test.in, got, test.expected)
		}
	}
}
