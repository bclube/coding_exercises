package solution

import (
	"aoc2023/common"
	"context"
	"strings"
)

// SolveDay14 solves the puzzle for day 14.
// It reads a byte grid from a file, cycles through the grid a billion times, and calculates the weight of the grid at each step.
// If it detects a repeating state, it calculates the start and length of the cycle and uses this to determine the state of the grid after a billion cycles.
func SolveDay14(ctx context.Context) (int, error) {
	// Read the byte grid from the file.
	platform, err := common.ReadByteGrid(ctx, "day14.txt")
	if err != nil {
		return 0, err
	}

	// Initialize maps to store the weight of the grid at each step and the order in which states appear.
	weights := make(map[int]int)
	inOrder := make(map[string]int)

	// Cycle through the grid a billion times.
	for i := 1; i <= 1_000_000_000; i++ {
		// Check if the context has been cancelled.
		if ctx.Err() != nil {
			return 0, ctx.Err()
		}

		// Perform a cycle on the platform.
		cycle(platform)

		// Convert the current state of the grid to a string.
		s := gridToString(platform)

		// If this state has not been seen before, store it in the inOrder map and calculate and store its weight.
		// If this state has been seen before, we have found a cycle.
		if _, ok := inOrder[s]; !ok {
			inOrder[s] = i
			weights[i] = calculateWeight(platform)
		} else {
			// Calculate the start and length of the cycle.
			cycleStart := inOrder[s]
			cycleLength := i - cycleStart

			// Calculate the index of the state of the grid after a billion cycles.
			idx := ((1_000_000_000 - cycleStart) % cycleLength) + cycleStart

			// Get the weight of the grid at this index.
			result := weights[idx]

			// Return the result.
			return result, nil
		}
	}

	// If we have not found a cycle after a billion cycles, return 0.
	return 0, nil
}

func gridToString(platform [][]byte) string {
	var builder strings.Builder
	for _, line := range platform {
		builder.WriteString(string(line))
		builder.WriteRune('\n')
	}
	return builder.String()
}

func cycle(platform [][]byte) {
	tilt(platform, north)
	tilt(platform, west)
	tilt(platform, south)
	tilt(platform, east)
}

type Direction int

const (
	north Direction = iota
	south
	east
	west
)

// slideRock moves a rock 'O' in the given direction on the platform until it hits an obstacle or the edge of the platform.
// The platform is represented as a 2D slice of bytes, where '.' represents an empty space and 'O' represents a rock.
// The function takes the initial position of the rock (row and col) and the direction in which to move the rock.
func slideRock(platform [][]byte, row, col int, direction Direction) {
	// Check if the initial position contains a rock. If not, return immediately.
	if platform[row][col] != 'O' {
		return
	}

	// Set the end and step variables based on the direction of movement.
	// If moving north or west, we need to iterate backwards, so set end to -1 and step to -1.
	// Otherwise, we're moving south or east, so set end to the length of the platform and step to 1.
	end, step := len(platform), 1
	if direction == north || direction == west {
		end, step = -1, -1
	}

	// Determine whether we're iterating over rows or columns based on the direction of movement.
	iter := &row
	if direction == east || direction == west {
		iter = &col
	}

	// Initialize the from and to positions to the initial position of the rock.
	fromRow, toRow, fromCol, toCol := row, row, col, col

	// Iterate over the platform in the given direction until we hit an obstacle or the edge of the platform.
	// Update the to position at each step.
	for *iter += step; *iter != end && platform[row][col] == '.'; *iter += step {
		toRow, toCol = row, col
	}

	// Clear the initial position of the rock and place the rock at the final position.
	platform[fromRow][fromCol] = '.'
	platform[toRow][toCol] = 'O'
}

// tilt moves all rocks 'O' in the given direction on the platform until they hit an obstacle or the edge of the platform.
// The platform is represented as a 2D slice of bytes, where '.' represents an empty space and 'O' represents a rock.
// The function takes the direction in which to tilt the platform.
func tilt(platform [][]byte, direction Direction) {
	// Set the start, end, and step variables for the row and column iterators.
	// By default, we iterate from the start to the end in the forward direction.
	rowStart, rowEnd, rowStep := 0, len(platform), 1
	colStart, colEnd, colStep := 0, len(platform[0]), 1

	// If the direction is south or east, we need to iterate from the end to the start in the backward direction.
	switch direction {
	case south:
		rowStart, rowEnd, rowStep = len(platform)-1, -1, -1
	case east:
		colStart, colEnd, colStep = len(platform[0])-1, -1, -1
	}

	// Iterate over the platform in the given direction.
	// For each position, if it contains a rock, slide it in the given direction.
	for row := rowStart; row != rowEnd; row += rowStep {
		for col := colStart; col != colEnd; col += colStep {
			slideRock(platform, row, col, direction)
		}
	}
}

// calculateWeight calculates the weight of the given grid.
// The weight is calculated as the sum of the distances of each rock from the bottom of the grid.
// The grid is represented as a 2D slice of bytes, where 'O' represents a rock.
func calculateWeight(grid [][]byte) int {
	var sum int
	for i, line := range grid {
		for _, cell := range line {
			if cell == 'O' {
				sum += len(grid) - i
			}
		}
	}
	return sum
}
