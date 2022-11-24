package problem01

import (
	"errors"
	"exercises/aoc2020/common"
	"strconv"
)

func Solve() (int, int, error) {
	inputFile := "./problem01/input.txt"
	resultA, err := SolveA(inputFile)
	if err != nil {
		return 0, 0, err
	}
	resultB, err := SolveB(inputFile)
	if err != nil {
		return 0, 0, err
	}
	return resultA, resultB, nil
}

func SolveA(inputFile string) (int, error) {
	lines, err := common.ParseFile(inputFile, strconv.Atoi)
	if err != nil {
		return 0, err
	}

	solutions := make(map[int]bool)
	for v := range lines {
		key := 2020 - v
		if _, exists := solutions[v]; exists {
			return v * key, nil
		} else {
			solutions[key] = true
		}
	}
	return 0, errors.New("unable to solve problem")
}

func SolveB(inputFile string) (int, error) {
	values, err := common.ParseFile(inputFile, strconv.Atoi)
	if err != nil {
		return 0, err
	}
	ints := common.ToSlice(values, 200)
	for i, a := range ints {
		for j, b := range ints {
			if i == j {
				continue
			}
			for k, c := range ints {
				if k == i || k == j {
					continue
				}
				if a+b+c == 2020 {
					return a * b * c, nil
				}
			}
		}
	}
	return 0, errors.New("unable to solve")
}
