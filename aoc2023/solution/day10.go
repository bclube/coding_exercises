package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
)

// TODO : Improve readability of this function.
func SolveDay10(ctx context.Context) (int, error) {
	lines, err := common.ReadAllLines(ctx, "day10.txt")
	if err != nil {
		return 0, err
	}
	start, err := findAnimal(lines)
	if err != nil {
		return 0, err
	}
	grid := make([][]byte, len(lines))
	for i, line := range lines {
		grid[i] = make([]byte, len(line))
		for j := range line {
			grid[i][j] = pipeGridUnmarked
		}
	}
	var totalTurnDiff int
	next := start
	for {
		select {
		case <-ctx.Done():
			return 0, ctx.Err()
		default:
		}
		var turn pipeGridTurn
		next, turn, err = traverseGridOneStep(lines, next)
		if err != nil {
			return 0, err
		}
		totalTurnDiff += int(turn)
		gridValue := lines[next.row][next.col]
		markGrid(grid, gridValue, next)
		if next.row == start.row && next.col == start.col {
			break
		}
	}
	// In a closed loop that does not intersect itself, there should be more 90-degree left
	// or 90-degree right turns than the other; the number of right and left turns should not
	// be equal. If there are more right turns, then we have a predominantly clockwise loop;
	// if there are more left turns, then we have a predominantly counter-clockwise loop.
	// If the loop is primarily clockwise, then the enclosed area is to the right of the path
	// (i.e. the grid cells we marked with 'r'); if the loop is primarily counter-clockwise,
	// then the enclosed area is to the left of the path (i.e. the grid cells we marked with 'l').
	var inside byte
	switch {
	case totalTurnDiff < 0:
		// More left turns. The loop is primarily counter-clockwise. The enclosed area is to the left of the path.
		inside = pipeGridLeft
	case totalTurnDiff > 0:
		// More right turns. The loop is primarily clockwise. The enclosed area is to the right of the path.
		inside = pipeGridRight
	default:
		panic(fmt.Sprintf("turn diff mismatch: %d", totalTurnDiff))
	}
	var enclosedCellCount int
	for _, row := range grid {
		insideEnclosedArea := false
		for _, cell := range row {
			if cell == inside {
				enclosedCellCount++
				insideEnclosedArea = true
			} else if insideEnclosedArea &&
				cell == pipeGridUnmarked {
				enclosedCellCount++
			} else {
				insideEnclosedArea = false
			}
		}
	}

	return enclosedCellCount, nil
}

func markCell(grid [][]byte, row, col int, b byte) {
	if row < 0 ||
		row >= len(grid) {
		return
	}
	gridRow := grid[row]
	if col < 0 ||
		col >= len(gridRow) {
		return
	}
	if gridRow[col] != pipeGridUnmarked {
		return
	}
	gridRow[col] = b
}

func markGrid(grid [][]byte, gridValue byte, t pipeGridTraverser) {
	// the cell that we're on is marked '.'
	// cells on our right are marked 'r'; cells on our left are marked 'l',
	// but we only do this if the cell is not already marked
	left, right := byte(pipeGridLeft), byte(pipeGridRight)
	grid[t.row][t.col] = pipeGridPath
	switch gridValue {
	case '|':
		if t.dir == pipeSouth {
			left, right = right, left
		}
		markCell(grid, t.row, t.col-1, left)
		markCell(grid, t.row, t.col+1, right)
	case '-':
		if t.dir == pipeWest {
			left, right = right, left
		}
		markCell(grid, t.row-1, t.col, left)
		markCell(grid, t.row+1, t.col, right)
	case 'F':
		if t.dir == pipeSouth {
			left = right
		}
		markCell(grid, t.row-1, t.col, left)
		markCell(grid, t.row-1, t.col-1, left)
		markCell(grid, t.row, t.col-1, left)
	case 'J':
		if t.dir == pipeNorth {
			left = right
		}
		markCell(grid, t.row+1, t.col, left)
		markCell(grid, t.row+1, t.col+1, left)
		markCell(grid, t.row, t.col+1, left)
	case '7':
		if t.dir == pipeWest {
			left = right
		}
		markCell(grid, t.row-1, t.col, left)
		markCell(grid, t.row-1, t.col+1, left)
		markCell(grid, t.row, t.col+1, left)
	case 'L':
		if t.dir == pipeEast {
			left = right
		}
		markCell(grid, t.row+1, t.col, left)
		markCell(grid, t.row+1, t.col-1, left)
		markCell(grid, t.row, t.col-1, left)
	}
}

var pipeDirections = map[struct {
	gridValue byte
	direction pipeDirection
}]pipeGridTurn{
	{'|', pipeNorth}: pipeGridStraight,
	{'|', pipeSouth}: pipeGridStraight,
	{'-', pipeWest}:  pipeGridStraight,
	{'-', pipeEast}:  pipeGridStraight,
	{'F', pipeNorth}: pipeGridTurnRight,
	{'F', pipeWest}:  pipeGridTurnLeft,
	{'J', pipeSouth}: pipeGridTurnRight,
	{'J', pipeEast}:  pipeGridTurnLeft,
	{'7', pipeNorth}: pipeGridTurnLeft,
	{'7', pipeEast}:  pipeGridTurnRight,
	{'L', pipeSouth}: pipeGridTurnLeft,
	{'L', pipeWest}:  pipeGridTurnRight,
}

func traverseGridOneStep(grid []string, t pipeGridTraverser) (
	next pipeGridTraverser,
	turn pipeGridTurn,
	err error,
) {
	next = t
	switch t.dir {
	case pipeNorth:
		next.row--
	case pipeSouth:
		next.row++
	case pipeWest:
		next.col--
	case pipeEast:
		next.col++
	}
	if next.row < 0 ||
		next.row >= len(grid) ||
		next.col < 0 ||
		next.col >= len(grid[next.row]) {
		err = fmt.Errorf("out of bounds")
		return
	}
	nextGridValue := grid[next.row][next.col]
	if nextGridValue == 'S' {
		return
	}
	var exists bool
	turn, exists = pipeDirections[struct {
		gridValue byte
		direction pipeDirection
	}{nextGridValue, t.dir}]
	if !exists {
		err = fmt.Errorf("invalid next position")
	}
	next.dir = (t.dir + 4 + pipeDirection(turn)) % __pipeDirectionSentinel__
	return
}

func findAnimal(grid []string) (pipeGridTraverser, error) {
	row, col, err := findAnimalStartPosition(grid)
	if err != nil {
		return pipeGridTraverser{}, err
	}
	animal := pipeGridTraverser{row, col, pipeNorth}
	for animal.dir = pipeNorth; animal.dir < __pipeDirectionSentinel__; animal.dir++ {
		if _, _, err := traverseGridOneStep(grid, animal); err == nil {
			return animal, nil
		}
	}
	return pipeGridTraverser{}, fmt.Errorf("invalid starting position")
}

func findAnimalStartPosition(grid []string) (int, int, error) {
	for row, gridRow := range grid {
		for col, gridCell := range gridRow {
			if gridCell == 'S' {
				return row, col, nil
			}
		}
	}
	return 0, 0, fmt.Errorf("no starting position found")
}

type pipeGridTraverser struct {
	row int
	col int
	dir pipeDirection
}

type pipeDirection uint8

const (
	pipeNorth pipeDirection = iota
	pipeEast
	pipeSouth
	pipeWest

	__pipeDirectionSentinel__
)

type pipeGridTurn int

const (
	pipeGridTurnLeft pipeGridTurn = iota - 1
	pipeGridStraight
	pipeGridTurnRight
)

const (
	pipeGridUnmarked = ' '
	pipeGridRight    = 'r'
	pipeGridLeft     = 'l'
	pipeGridPath     = '.'
)
