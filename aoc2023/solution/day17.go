package solution

import (
	"aoc2023/common"
	"container/heap"
	"context"
	"fmt"
	"math"
)

func SolveDay17(ctx context.Context) (int, error) {
	grid, err := common.ReadAllLines(ctx, "day17.txt")
	if err != nil {
		return 0, err
	}
	return FindMinimalPath(ctx, grid)
}

const maxTurn = 10
const minTurn = 4
const turnDiff = maxTurn - minTurn

func FindMinimalPath(ctx context.Context, grid []string) (int, error) {
	bestSoFar := make([][][4][maxTurn]lavaCrucible, len(grid))
	for i, line := range grid {
		bestSoFar[i] = make([][4][maxTurn]lavaCrucible, len(line))
	}
	traversers := make(lavaCrucibleHeap, 0, len(grid)*3)
	heap.Push(&traversers, lavaCrucible{row: 0, col: 0, dir: lavaCrucibleSouth, turnTimeout: maxTurn})
	heap.Push(&traversers, lavaCrucible{row: 0, col: 0, dir: lavaCrucibleEast, turnTimeout: maxTurn})
	for len(traversers) > 0 {
		if ctx.Err() != nil {
			return 0, ctx.Err()
		}
		crucible := heap.Pop(&traversers).(lavaCrucible)
		for d := lavaCrucibleLeft; d <= lavaCrucibleRight; d++ {
			copy := crucible
			err := copy.turn(d)
			if err != nil {
				continue
			}
			err = copy.advance(grid)
			if err != nil {
				continue
			}
			best := &bestSoFar[copy.row][copy.col][copy.dir][copy.turnTimeout]
			if best.heatLoss != 0 && best.heatLoss <= copy.heatLoss {
				continue
			}
			*best = copy
			if copy.row == len(grid)-1 && copy.col == len(grid[0])-1 {
				continue
			}
			heap.Push(&traversers, copy)
		}
	}
	leastHeatLoss := math.MaxInt
	for _, bbest := range bestSoFar[len(grid)-1][len(grid[0])-1] {
		for _, best := range bbest {
			if best.heatLoss != 0 && best.heatLoss < leastHeatLoss {
				leastHeatLoss = best.heatLoss
			}
		}
	}
	return leastHeatLoss, nil
}

func (l *lavaCrucible) turn(turn lavaCricibleTurn) error {
	if turn != lavaCrucibleStraight && l.turnTimeout > turnDiff {
		return errCantTurnYet
	}
	newDir := (l.dir + __lavaCrucibleDirectionMax__ + lavaCrucibleDirection(turn)) % __lavaCrucibleDirectionMax__
	if newDir != l.dir {
		l.dir = newDir
		l.turnTimeout = maxTurn
	}
	return nil
}

func (l *lavaCrucible) advance(grid []string) error {
	if l.turnTimeout == 0 {
		return errTurnTimeout
	}
	switch l.dir {
	case lavaCrucibleNorth:
		l.row--
	case lavaCrucibleEast:
		l.col++
	case lavaCrucibleSouth:
		l.row++
	case lavaCrucibleWest:
		l.col--
	}
	if l.row < 0 || l.row >= len(grid) || l.col < 0 || l.col >= len(grid[0]) {
		return errOutOfBounds
	}
	heatLoss := grid[l.row][l.col] - '0'
	l.heatLoss += int(heatLoss)
	l.turnTimeout--
	return nil
}

var errCantTurnYet = fmt.Errorf("can't turn yet")
var errOutOfBounds = fmt.Errorf("out of bounds")
var errTurnTimeout = fmt.Errorf("turn timeout")

type lavaCricibleTurn int8

const (
	lavaCrucibleLeft lavaCricibleTurn = iota - 1
	lavaCrucibleStraight
	lavaCrucibleRight
)

type lavaCrucibleDirection int8

const (
	lavaCrucibleNorth lavaCrucibleDirection = iota
	lavaCrucibleEast
	lavaCrucibleSouth
	lavaCrucibleWest

	__lavaCrucibleDirectionMax__
)

type lavaCrucible struct {
	heatLoss    int
	row, col    int
	dir         lavaCrucibleDirection
	turnTimeout int
}

type lavaCrucibleHeap []lavaCrucible

func (h lavaCrucibleHeap) Len() int           { return len(h) }
func (h lavaCrucibleHeap) Less(i, j int) bool { return h[i].heatLoss < h[j].heatLoss }
func (h lavaCrucibleHeap) Swap(i, j int)      { h[i], h[j] = h[j], h[i] }
func (h *lavaCrucibleHeap) Push(x interface{}) {
	*h = append(*h, x.(lavaCrucible))
}
func (h *lavaCrucibleHeap) Pop() interface{} {
	old := *h
	n := len(old)
	x := old[n-1]
	*h = old[:n-1]
	return x
}
