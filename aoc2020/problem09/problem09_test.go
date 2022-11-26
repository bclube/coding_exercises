package problem09

import "testing"

func TestSolveA(t *testing.T) {
	in := "../testdata/input09.txt"
	expected := 127
	got, _, err := SolveBoth(in, 5)
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
		{in: "../testdata/input09.txt", expected: 62},
	}
	for _, test := range tests {
		_, got, err := SolveBoth(test.in, 5)
		if err != nil {
			t.Errorf(err.Error())
		} else if got != test.expected {
			t.Errorf("SolveBoth<<B>>(%q) == %d; expected %d", test.in, got, test.expected)
		}
	}
}
