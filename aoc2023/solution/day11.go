package solution

import (
	"aoc2023/common"
	"context"
)

func SolveDay11(ctx context.Context) (int, error) {
	starField, err := common.ReadAllLines(ctx, "day11.txt")
	if err != nil {
		return 0, err
	}
	rowDistanceSum := countDistance(starField, true)
	colDistanceSum := countDistance(starField, false)
	return rowDistanceSum + colDistanceSum, nil
}

func countDistance(starField []string, isRow bool) int {
	var galaxyCount, distanceSum, marginalDistance int
	maxOuter, maxInner := len(starField), len(starField[0])
	if !isRow {
		maxOuter, maxInner = maxInner, maxOuter
	}
	for i := 0; i < maxOuter; i++ {
		var count int
		for j := 0; j < maxInner; j++ {
			var cell byte
			if isRow {
				cell = starField[i][j]
			} else {
				cell = starField[j][i]
			}
			if cell == '#' {
				count++
			}
		}
		distanceSum += count * marginalDistance
		galaxyCount += count
		expansionFactor := 1
		if count == 0 {
			expansionFactor = 1_000_000
		}
		marginalDistance += galaxyCount * expansionFactor
	}
	return distanceSum
}
