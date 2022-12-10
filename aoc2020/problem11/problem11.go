package problem11

import (
	"exercises/aoc2020/common"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem11/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	seatMap, maxRow, maxCol, err := parseFile(inputFile)
	if err != nil {
		return 0, 0, err
	}
	solutionA := solve(seatMap, maxRow, maxCol, true, 4)
	solutionB := solve(seatMap, maxRow, maxCol, false, 5)
	return solutionA, solutionB, nil
}

func solve(seatMap map[seatLocation]bool, maxRow, maxCol int, limitSightLine bool, occupancyLimit int) int {
	adjacencyMap := makeAdjacencyMap(seatMap, maxRow, maxCol, limitSightLine)
	finalMap := runSimulation(seatMap, adjacencyMap, occupancyLimit)
	solutionA := 0
	for _, v := range finalMap {
		if v {
			solutionA++
		}
	}
	return solutionA
}

var offsets = []struct {
	row int
	col int
}{
	{row: -1, col: -1},
	{row: -1, col: 0},
	{row: -1, col: 1},
	{row: 0, col: -1},
	{row: 0, col: 1},
	{row: 1, col: -1},
	{row: 1, col: 0},
	{row: 1, col: 1},
}

func makeAdjacencyMap(seatMap map[seatLocation]bool, maxRow, maxCol int, limitSightLine bool) map[seatLocation][]seatLocation {
	adjacencyMap := map[seatLocation][]seatLocation{}
	for seat, _ := range seatMap {
		adjacencyList := []seatLocation{}
		for _, offset := range offsets {
			candidate := seat
			for {
				candidate.row += offset.row
				candidate.col += offset.col
				if _, exists := seatMap[candidate]; exists {
					adjacencyList = append(adjacencyList, candidate)
					break
				}
				if limitSightLine {
					break
				}
				if candidate.row < 0 || candidate.row >= maxRow || candidate.col < 0 || candidate.col >= maxCol {
					break
				}
			}
		}
		adjacencyMap[seat] = adjacencyList
	}
	return adjacencyMap
}

func runSimulation(seatMap map[seatLocation]bool, adjacencyMap map[seatLocation][]seatLocation, occupancyLimit int) map[seatLocation]bool {
	solvedSeats := map[seatLocation]bool{}
	for len(seatMap) > 0 {
		newMap := map[seatLocation]bool{}
		for seat, occupied := range seatMap {
			if !occupied {
				solvedSeats[seat] = false
			} else {
				newMap[seat] = stayPut(seat, seatMap, adjacencyMap, occupancyLimit)
			}
		}
		seatMap, newMap = newMap, map[seatLocation]bool{}
		for seat, occupied := range seatMap {
			if occupied {
				solvedSeats[seat] = true
			} else {
				newMap[seat] = sit(seat, seatMap, adjacencyMap)
			}
		}
		seatMap = newMap
	}
	return solvedSeats
}

func stayPut(seat seatLocation, seatMap map[seatLocation]bool, adjacencyMap map[seatLocation][]seatLocation, occupancyLimit int) bool {
	occupantCount := 0
	for _, adjacentSeat := range adjacencyMap[seat] {
		if _, exists := seatMap[adjacentSeat]; exists {
			occupantCount++
		}
	}
	return occupantCount < occupancyLimit
}

func sit(seat seatLocation, seatMap map[seatLocation]bool, adjacencyMap map[seatLocation][]seatLocation) bool {
	for _, adjacentSeat := range adjacencyMap[seat] {
		if seatMap[adjacentSeat] {
			return false
		}
	}
	return true
}

type seatLocation struct {
	row int
	col int
}

func parseFile(inputFile string) (map[seatLocation]bool, int, int, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return nil, 0, 0, err
	}
	result := map[seatLocation]bool{}
	row := -1
	maxCol := -1
	for line := range lines {
		row++
		if len(line) > maxCol {
			maxCol = len(line)
		}
		for col, char := range line {
			if char == 'L' {
				coord := seatLocation{row: row, col: col}
				result[coord] = true
			}
		}
	}
	return result, row + 1, maxCol, nil
}
