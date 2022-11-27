package problem10

import (
	"exercises/aoc2020/common"
	"sort"
	"strconv"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem10/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	ints, err := common.ParseFile(inputFile, strconv.Atoi)
	if err != nil {
		return 0, 0, err
	}
	joltages := []int{0}
	for joltage := range ints {
		joltages = append(joltages, joltage)
	}
	sort.Ints(joltages)
	joltages = append(joltages, joltages[len(joltages)-1]+3)
	solutionA := solveA(joltages)
	solutionB := solveB(joltages)
	return solutionA, solutionB, nil
}

func solveA(joltages []int) int {
	ones := 0
	threes := 0
	for i := 1; i < len(joltages); i++ {
		diff := joltages[i] - joltages[i-1]
		if diff == 1 {
			ones++
		} else if diff == 3 {
			threes++
		}
	}
	return ones * threes
}

func solveB(joltages []int) int {
	path_counts := map[int]int{
		0: 1,
	}
	var path_count int
	for _, joltageAdapter := range joltages {
		path_count = path_counts[joltageAdapter]
		path_counts[joltageAdapter+1] += path_count
		path_counts[joltageAdapter+2] += path_count
		path_counts[joltageAdapter+3] += path_count
	}
	return path_count
}
