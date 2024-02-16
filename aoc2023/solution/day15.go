package solution

import (
	"aoc2023/common"
	"context"
	"sort"
	"strings"
)

func SolveDay15(ctx context.Context) (int, error) {
	lines, err := common.ReadAllLines(ctx, "day15.txt")
	if err != nil {
		return 0, err
	}
	split := strings.Split(lines[0], ",")
	lenses := make(map[string]lens, 400)
	for i, s := range split {
		if s[len(s)-1] == '-' {
			delete(lenses, s[:len(s)-1])
		} else {
			label := s[:len(s)-2]
			focalLength := s[len(s)-1] - '0'
			l := lenses[label]
			if l.order == 0 {
				l.order = i
			}
			l.focalLength = focalLength
			lenses[label] = l
		}
	}
	lensBoxes := [256][]lens{}
	for k, v := range lenses {
		h := ComputeHash(k)
		lensBoxes[h] = append(lensBoxes[h], v)
	}
	var sum int
	for boxNumber, lensBox := range lensBoxes {
		sort.Slice(lensBox, func(j, k int) bool {
			return lensBox[j].order < lensBox[k].order
		})
		for slotNumber, lens := range lensBox {
			sum += (boxNumber + 1) * (slotNumber + 1) * int(lens.focalLength)
		}
	}

	return sum, nil
}

func ComputeHash(input string) byte {
	var hash int
	for i := range input {
		hash += int(input[i])
		hash *= 17
		hash %= 256
	}
	return byte(hash)
}

type lens struct {
	focalLength byte
	order       int
}
