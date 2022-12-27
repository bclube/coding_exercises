package problem19

import "testing"

func TestSolveBoth(t *testing.T) {
	tests := []struct {
		in       string
		expected int
	}{
		{in: "../testdata/input19.txt", expected: 12},
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
