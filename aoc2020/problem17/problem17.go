package problem17

import (
	"exercises/aoc2020/common"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem17/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	grid3, grid4, err := parseFile(inputFile)
	if err != nil {
		return 0, 0, err
	}
	for i := 0; i < 6; i++ {
		grid3 = iterate3(grid3)
		grid4 = iterate4(grid4)
	}
	return len(grid3), len(grid4), nil
}

func iterate4(space map[coord4]bool) map[coord4]bool {
	result := map[coord4]bool{}
	counts := map[coord4]int{}
	for coord := range space {
		adjacencyCount := 0
		for x := -1; x <= 1; x++ {
			for y := -1; y <= 1; y++ {
				for z := -1; z <= 1; z++ {
					for w := -1; w <= 1; w++ {
						if x == 0 && y == 0 && z == 0 && w == 0 {
							continue
						}
						checkCoord := coord4{coord.x + x, coord.y + y, coord.z + z, coord.w + w}
						if space[checkCoord] {
							adjacencyCount++
						}
						counts[checkCoord]++
					}
				}
			}
		}
		if adjacencyCount == 2 || adjacencyCount == 3 {
			result[coord] = true
		}
	}
	for coord, count := range counts {
		if count == 3 {
			result[coord] = true
		}
	}
	return result
}

func iterate3(space map[coord3]bool) map[coord3]bool {
	result := map[coord3]bool{}
	counts := map[coord3]int{}
	for coord := range space {
		adjacencyCount := 0
		for x := -1; x <= 1; x++ {
			for y := -1; y <= 1; y++ {
				for z := -1; z <= 1; z++ {
					if x == 0 && y == 0 && z == 0 {
						continue
					}
					checkCoord := coord3{coord.x + x, coord.y + y, coord.z + z}
					if space[checkCoord] {
						adjacencyCount++
					}
					counts[checkCoord]++
				}
			}
		}
		if adjacencyCount == 2 || adjacencyCount == 3 {
			result[coord] = true
		}
	}
	for coord, count := range counts {
		if count == 3 {
			result[coord] = true
		}
	}
	return result
}

type coord3 struct {
	x int
	y int
	z int
}

type coord4 struct {
	x int
	y int
	z int
	w int
}

func parseFile(inputFile string) (map[coord3]bool, map[coord4]bool, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return nil, nil, err
	}
	result3 := map[coord3]bool{}
	result4 := map[coord4]bool{}
	x := -1
	for line := range lines {
		x++
		for y, c := range line {
			if c == '#' {
				result3[coord3{x, y, 0}] = true
				result4[coord4{x, y, 0, 0}] = true
			}
		}
	}
	return result3, result4, nil
}
