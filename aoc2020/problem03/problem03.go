package problem03

import (
	"exercises/aoc2020/common"
)

func Solve() (int, int, error) {
	inputFile := "./problem03/input.txt"
	resultA, resultB, err := SolveBoth(inputFile)
	if err != nil {
		return 0, 0, err
	}
	return resultA, resultB, nil
}

func SolveBoth(inputFile string) (int, int, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return 0, 0, err
	}
	tobogganists := []*Tobogganist{
		NewTobogganist(3, 1),
		NewTobogganist(1, 1),
		NewTobogganist(5, 1),
		NewTobogganist(7, 1),
		NewTobogganist(1, 2),
	}
	for mapRow := range lines {
		for _, tobogganist := range tobogganists {
			tobogganist.SledARow(mapRow)
		}
	}
	product := 1
	for _, tobogganist := range tobogganists {
		product *= tobogganist.treeImpacts
	}
	return tobogganists[0].treeImpacts, product, nil
}

type Tobogganist struct {
	xVelocity   int
	yVelocity   int
	xPosition   int
	yPosition   int
	treeImpacts int
}

func NewTobogganist(x_velocity, y_velocity int) *Tobogganist {
	return &Tobogganist{
		xVelocity:   x_velocity,
		yVelocity:   y_velocity,
		xPosition:   -x_velocity,
		yPosition:   -1,
		treeImpacts: 0,
	}
}

func (tb *Tobogganist) SledARow(row string) {
	const tree = '#'
	tb.yPosition++
	if tb.yPosition%tb.yVelocity == 0 {
		tb.xPosition = (tb.xPosition + tb.xVelocity) % len(row)
		if row[tb.xPosition] == tree {
			tb.treeImpacts++
		}
	}
}
