package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
	"time"
)

func SolveDay16(ctx context.Context) (int, error) {
	grid, err := common.ReadByteGrid(ctx, "day16.txt")
	if err != nil {
		return 0, err
	}
	start := time.Now()
	var max int
	for col := range grid[0] {
		t := mirrorGridTraverser{row: 0, col: col, dir: mirrorGridDown}
		spaceCount := countActivatedTiles(t, grid)
		if spaceCount > max {
			max = spaceCount
		}
		t.row = len(grid[0]) - 1
		t.dir = mirrorGridUp
		spaceCount = countActivatedTiles(t, grid)
		if spaceCount > max {
			max = spaceCount
		}
	}
	for row := range grid {
		t := mirrorGridTraverser{row: row, col: 0, dir: mirrorGridRight}
		spaceCount := countActivatedTiles(t, grid)
		if spaceCount > max {
			max = spaceCount
		}
		t.col = len(grid) - 1
		t.dir = mirrorGridLeft
		spaceCount = countActivatedTiles(t, grid)
		if spaceCount > max {
			max = spaceCount
		}
	}
	fmt.Println(time.Since(start))
	return max, nil
}

func countActivatedTiles(from mirrorGridTraverser, grid [][]byte) int {
	tracking := make([][]mirrorGridDirection, len(grid))
	for i, row := range grid {
		tracking[i] = make([]mirrorGridDirection, len(row))
	}
	traversers := make([]mirrorGridTraverser, 1, 50)
	traversers[0] = from

	for len(traversers) > 0 {
		traverser := &traversers[len(traversers)-1]
		if traverser.row < 0 || traverser.row >= len(tracking) ||
			traverser.col < 0 || traverser.col >= len(tracking[0]) ||
			tracking[traverser.row][traverser.col]&traverser.dir != 0 {
			traversers = traversers[:len(traversers)-1]
			continue
		}
		tracking[traverser.row][traverser.col] |= traverser.dir
		switch grid[traverser.row][traverser.col] {
		case '.':
			switch traverser.dir {
			case mirrorGridUp:
				traverser.row--
			case mirrorGridDown:
				traverser.row++
			case mirrorGridLeft:
				traverser.col--
			case mirrorGridRight:
				traverser.col++
			}
		case '/':
			switch traverser.dir {
			case mirrorGridUp:
				traverser.dir = mirrorGridRight
				traverser.col++
			case mirrorGridDown:
				traverser.dir = mirrorGridLeft
				traverser.col--
			case mirrorGridLeft:
				traverser.dir = mirrorGridDown
				traverser.row++
			case mirrorGridRight:
				traverser.dir = mirrorGridUp
				traverser.row--
			}
		case '\\':
			switch traverser.dir {
			case mirrorGridUp:
				traverser.dir = mirrorGridLeft
				traverser.col--
			case mirrorGridDown:
				traverser.dir = mirrorGridRight
				traverser.col++
			case mirrorGridLeft:
				traverser.dir = mirrorGridUp
				traverser.row--
			case mirrorGridRight:
				traverser.dir = mirrorGridDown
				traverser.row++
			}
		case '|':
			switch traverser.dir {
			case mirrorGridUp:
				traverser.row--
			case mirrorGridDown:
				traverser.row++
			case mirrorGridLeft, mirrorGridRight:
				traverser.dir = mirrorGridUp
				traverser.row--
				traversers = append(traversers, mirrorGridTraverser{traverser.row + 2, traverser.col, mirrorGridDown})
			}
		case '-':
			switch traverser.dir {
			case mirrorGridLeft:
				traverser.col--
			case mirrorGridRight:
				traverser.col++
			case mirrorGridUp, mirrorGridDown:
				traverser.dir = mirrorGridLeft
				traverser.col--
				traversers = append(traversers, mirrorGridTraverser{traverser.row, traverser.col + 2, mirrorGridRight})
			}
		}
	}

	var spaceCount int
	for _, line := range tracking {
		for _, cell := range line {
			if cell == 0 {
				continue
			}
			spaceCount++
		}

	}
	return spaceCount
}

type mirrorGridDirection uint8

const (
	mirrorGridUp mirrorGridDirection = (1 << iota)
	mirrorGridDown
	mirrorGridLeft
	mirrorGridRight
)

type mirrorGridTraverser struct {
	row int
	col int
	dir mirrorGridDirection
}
