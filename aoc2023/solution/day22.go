package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
	"maps"
	"slices"
)

func SolveDay22(ctx context.Context) (int, error) {
	lines, err := common.ReadAllLines(ctx, "day22.txt")
	if err != nil {
		return 0, err
	}
	bricks := make([]sandBrick, len(lines))
	for i, line := range lines {
		err := parseSandBrick(line, &bricks[i])
		if err != nil {
			return 0, err
		}
	}
	slices.SortFunc(bricks, orderByZ)
	base := [10][10]*brickSiloBase{}
	var fallingBrickCount int
	for id, brick := range bricks {
		supporters := make(map[int]struct{}, 10)
		uniqueSupporters := make(map[int]struct{}, 150)
		newBrick := brickSiloBase{id: id, uniqueSupporters: uniqueSupporters}
		var initialized bool
		for x := brick.begin.x; x <= brick.end.x; x++ {
			for y := brick.begin.y; y <= brick.end.y; y++ {
				before := base[x][y]
				base[x][y] = &newBrick
				switch {
				case before == nil:
				case before.z > newBrick.z:
					newBrick.z = before.z
					clear(supporters)
					clear(uniqueSupporters)
					initialized = false
					fallthrough
				case before.z == newBrick.z:
					if !initialized {
						maps.Copy(uniqueSupporters, before.uniqueSupporters)
						initialized = true
					} else {
						for k := range uniqueSupporters {
							if _, ok := before.uniqueSupporters[k]; !ok {
								delete(uniqueSupporters, k)
							}
						}
					}
					supporters[before.id] = struct{}{}
				}
			}
		}
		newBrick.z += 1 + brick.end.z - brick.begin.z
		if len(supporters) == 1 {
			maps.Copy(uniqueSupporters, supporters)
		}
		fallingBrickCount += len(uniqueSupporters)
	}
	return fallingBrickCount, nil
}

func parseSandBrick(line string, brick *sandBrick) error {
	n, err := fmt.Sscanf(line, "%d,%d,%d~%d,%d,%d",
		&brick.begin.x, &brick.begin.y, &brick.begin.z,
		&brick.end.x, &brick.end.y, &brick.end.z)
	if err != nil {
		return err
	}
	if n != 6 {
		return fmt.Errorf("expected 6 values, got %d", n)
	}
	// always ensuring that begin.z <= end.z makes logic simpler elsewhere, but doesn't affect the final result
	if brick.begin.z > brick.end.z {
		brick.begin.z, brick.end.z = brick.end.z, brick.begin.z
	}
	return nil
}

func orderByZ(a, b sandBrick) int {
	// assumes that the z coords are sorted (i.e. .begin.z <= .end.z)
	return a.begin.z - b.begin.z
}

type brickSiloBase struct {
	z                int
	id               int
	uniqueSupporters map[int]struct{}
}

type sandBrick struct {
	begin, end sandBrickCoordinate
}

type sandBrickCoordinate struct {
	x, y, z int
}
