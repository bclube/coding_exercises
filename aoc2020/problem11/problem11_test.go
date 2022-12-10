package problem11

import "testing"

func TestSolveA(t *testing.T) {
	tests := []struct {
		in       string
		expected int
	}{
		{in: "../testdata/input11.txt", expected: 37},
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
		in       string
		expected int
	}{
		{in: "../testdata/input11.txt", expected: 26},
	}
	for _, test := range tests {
		_, got, err := SolveBoth(test.in)
		if err != nil {
			t.Errorf(err.Error())
		} else if got != test.expected {
			t.Errorf("SolveBoth<<B>>(%q) == %d; expected %d", test.in, got, test.expected)
		}
	}
}
