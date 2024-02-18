package solution

import (
	"aoc2023/common"
	"context"
	"strconv"

	"golang.org/x/sync/errgroup"
)

func SolveDay18(ctx context.Context) (int, error) {
	g, ctx := errgroup.WithContext(ctx)
	lines, lineReader := common.LinesFromFile(ctx, "day18.txt")
	parsedLines, lineParser := common.MapValues(ctx, lines, parseTrenchInstruction)
	g.Go(lineReader)
	g.Go(lineParser)
	var row, col int
	var borderSquares int
	var xyProductSum, yxProductSum int
	g.Go(common.ForEach(ctx, parsedLines, func(ctx context.Context, instruction trenchInstruction) error {
		borderSquares += int(instruction.magnitude)
		prevRow, prevCol := row, col
		row += int(instruction.upDown)
		col += int(instruction.leftRight)
		xyProductSum += prevRow * col
		yxProductSum += prevCol * row
		return nil
	}))
	if err := g.Wait(); err != nil {
		return 0, err
	}
	// calculate inner area using the shoelace formula
	shoelaceArea := (xyProductSum - yxProductSum) / 2
	if shoelaceArea < 0 {
		shoelaceArea = -shoelaceArea
	}
	// calculate the border area, based on the number of border squares
	borderArea := (borderSquares / 2) + 1
	totalArea := shoelaceArea + borderArea
	return totalArea, nil
}

func parseTrenchInstruction(ctx context.Context, line string) (
	result trenchInstruction,
	err error,
) {
	hexLength := line[len(line)-7 : len(line)-2]
	result.magnitude, err = strconv.ParseInt(hexLength, 16, 32)
	if err != nil {
		return
	}
	switch line[len(line)-2] {
	case '0':
		result.leftRight = result.magnitude
	case '1':
		result.upDown = result.magnitude
	case '2':
		result.leftRight = -result.magnitude
	case '3':
		result.upDown = -result.magnitude
	}
	if err != nil {
		return
	}
	return
}

type trenchInstruction struct {
	magnitude int64
	leftRight int64
	upDown    int64
}
