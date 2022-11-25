package problem04

import "testing"

func TestSolveA(t *testing.T) {
	in := "../testdata/input04.txt"
	expected := 2
	got, _, err := SolveBoth(in)
	if err != nil {
		t.Errorf(err.Error())
	}
	if got != expected {
		t.Errorf("SolveBoth<<A>>(%q) == %d; expected %d", in, got, expected)
	}
}

func TestSolveB(t *testing.T) {
	in := "../testdata/input04b.txt"
	expected := 4
	_, got, err := SolveBoth(in)
	if err != nil {
		t.Errorf(err.Error())
	}
	if got != expected {
		t.Errorf("SolveBoth<<B>>(%q) == %d; expected %d", in, got, expected)
	}
}
