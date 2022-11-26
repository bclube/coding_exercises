package problem09

import (
	"errors"
	"exercises/aoc2020/common"
	"strconv"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem09/input.txt", 25)
}

func SolveBoth(inputFile string, preambleLength int) (int, int, error) {
	ints, err := common.ParseFile(inputFile, strconv.Atoi)
	if err != nil {
		return 0, 0, err
	}
	numbers := []int{}
	for number := range ints {
		numbers = append(numbers, number)
	}
	solutionA, err := solveA(numbers, preambleLength)
	if err != nil {
		return solutionA, 0, err
	}
	solutionB, err := solveB(numbers, solutionA)
	return solutionA, solutionB, err
}

func solveA(ints []int, preambleLength int) (int, error) {
	for i := preambleLength; i < len(ints); i++ {
		number := ints[i]
		solutions := map[int]bool{}
		found_solution := false
		for p := i - preambleLength; p < i; p++ {
			value := ints[p]
			if _, found_solution = solutions[value]; found_solution {
				break
			}
			solutions[number-value] = true
		}
		if !found_solution {
			return number, nil
		}
	}
	return 0, errors.New("unable to find solution")
}

func solveB(numbers []int, solutionA int) (int, error) {
	bi := 0
	ei := 0
	sum := 0
	for bi < len(numbers) && ei < len(numbers) {
		if sum < solutionA {
			sum += numbers[ei]
			ei++
		} else if sum > solutionA {
			sum -= numbers[bi]
			bi++
		} else {
			min := sum
			max := 0
			for i := bi; i < ei; i++ {
				number := numbers[i]
				if number < min {
					min = number
				}
				if number > max {
					max = number
				}
			}
			return min + max, nil
		}
	}
	return 0, errors.New("unable to find solution")
}
