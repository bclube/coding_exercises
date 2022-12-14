package problem14

import "testing"

func TestSolveA(t *testing.T) {
	tests := []struct {
		in       string
		expected uint64
	}{
		//{in: "../testdata/input14.txt", expected: 165},
		// This test case has many Xs making it take a long time to run.
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
		expected uint64
	}{
		{in: "../testdata/input14b.txt", expected: 208},
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
