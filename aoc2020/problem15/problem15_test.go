package problem15

import "testing"

func TestSolveA(t *testing.T) {
	tests := []struct {
		ints     []int
		expected int
	}{
		{ints: []int{0, 3, 6}, expected: 436},
		{ints: []int{1, 3, 2}, expected: 1},
		{ints: []int{2, 1, 3}, expected: 10},
		{ints: []int{1, 2, 3}, expected: 27},
		{ints: []int{2, 3, 1}, expected: 78},
		{ints: []int{3, 2, 1}, expected: 438},
		{ints: []int{3, 1, 2}, expected: 1836},
	}
	for _, test := range tests {
		got, _, err := SolveBoth(test.ints)
		if err != nil {
			t.Errorf(err.Error())
		} else if got != test.expected {
			t.Errorf("SolveBoth<<A>>(%v) == %d; expected %d", test.ints, got, test.expected)
		}
	}
}

func TestSolveB(t *testing.T) {
	tests := []struct {
		ints     []int
		expected int
	}{
		{ints: []int{0, 3, 6}, expected: 175594},
		{ints: []int{1, 3, 2}, expected: 2578},
		{ints: []int{2, 1, 3}, expected: 3544142},
		{ints: []int{1, 2, 3}, expected: 261214},
		{ints: []int{2, 3, 1}, expected: 6895259},
		{ints: []int{3, 2, 1}, expected: 18},
		{ints: []int{3, 1, 2}, expected: 362},
	}
	for _, test := range tests {
		_, got, err := SolveBoth(test.ints)
		if err != nil {
			t.Errorf(err.Error())
		} else if got != test.expected {
			t.Errorf("SolveBoth<<B>>(%v) == %d; expected %d", test.ints, got, test.expected)
		}
	}
}
