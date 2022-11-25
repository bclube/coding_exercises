package problem05

import "testing"

func TestFileSeatId(t *testing.T) {
	tests := []struct {
		input    string
		expected int
	}{
		{input: "BFFFBBFRRR", expected: 567},
		{input: "FFFBBBFRRR", expected: 119},
		{input: "BBFFBBFRLL", expected: 820},
	}
	for _, tt := range tests {
		if got, err := FindSeatId(tt.input); got != tt.expected {
			if err != nil {
				t.Error(err.Error())
			} else {
				t.Errorf("FindSeatId(%v) = %v, want %v", tt.input, got, tt.expected)
			}
		}
	}
}
