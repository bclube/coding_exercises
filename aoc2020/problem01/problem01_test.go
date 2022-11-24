package problem01

import (
	"testing"
)

func TestSolveA(t *testing.T) {
	in := "../testdata/input01.txt"
	expected := 514579
	got, err := SolveA(in)
	if err != nil {
		t.Errorf(err.Error())
	}
	if got != expected {
		t.Errorf("SolveA(%q) == %d; expected %d", in, got, expected)
	}
}

func TestSolveB(t *testing.T) {
	in := "../testdata/input01.txt"
	expected := 241861950
	got, err := SolveB(in)
	if err != nil {
		t.Errorf(err.Error())
	}
	if got != expected {
		t.Errorf("SolveB(%q) == %d; expected %d", in, got, expected)
	}
}
