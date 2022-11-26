package problem06

import (
	"exercises/aoc2020/common"
	"math"
	"math/bits"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem06/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	results, err := parseFile(inputFile)
	if err != nil {
		return 0, 0, err
	}
	solutionA := 0
	solutionB := 0
	for result := range results {
		solutionA += bits.OnesCount32(result.any)
		solutionB += bits.OnesCount32(result.every)
	}
	return solutionA, solutionB, nil
}

type answerSet struct {
	every uint32
	any   uint32
}

func parseFile(inputFile string) (<-chan answerSet, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return nil, err
	}
	out := make(chan answerSet)
	go func() {
		defer close(out)
		current_batch := answerSet{any: 0, every: math.MaxUint32}
		for line := range lines {
			if len(line) == 0 && current_batch.any != 0 {
				out <- current_batch
				current_batch = answerSet{any: 0, every: math.MaxUint32}
			} else {
				var this uint32 = 0
				for _, char := range line {
					this |= 1 << (char - 'a')
				}
				current_batch.any |= this
				current_batch.every &= this
			}
		}
		if current_batch.any != 0 {
			out <- current_batch
		}
	}()
	return out, err
}
