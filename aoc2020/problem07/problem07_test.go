package problem07

import "testing"

func TestSolveA(t *testing.T) {
	in := "../testdata/input07.txt"
	expected := 4
	got, _, err := SolveBoth(in)
	if err != nil {
		t.Errorf(err.Error())
	}
	if got != expected {
		t.Errorf("SolveBoth<<A>>(%q) == %d; expected %d", in, got, expected)
	}
}

func TestSolveB(t *testing.T) {
	tests := []struct {
		in       string
		expected int
	}{
		{in: "../testdata/input07.txt", expected: 32},
		{in: "../testdata/input07b.txt", expected: 126},
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
