package problem18

import "testing"

func TestSolve(t *testing.T) {
	tests := []struct {
		in       string
		expected int
	}{
		{in: "1 + 2 * 3 + 4 * 5 + 6", expected: 231},
		{in: "1 + (2 * 3) + (4 * (5 + 6))", expected: 51},
		{in: "2 * 3 + (4 * 5)", expected: 46},
		{in: "5 + (8 * 3 + 9 + 3 * 4 * 3)", expected: 1445},
		{in: "5 * 9 * (7 * 3 * 3 + 9 * 3 + (8 + 6 * 4))", expected: 669060},
		{in: "((2 + 4 * 9) * (6 + 9 * 8 + 6) + 6) + 2 + 4 * 2", expected: 23340},
	}
	for _, test := range tests {
		got, err := Compute(test.in)
		if err != nil {
			t.Errorf(err.Error())
		} else if got != test.expected {
			t.Errorf("SolveBoth<<B>>(%q) == %d; expected %d", test.in, got, test.expected)
		}
	}
}
