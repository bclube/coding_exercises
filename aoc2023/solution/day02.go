package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
	"regexp"
	"strconv"

	"golang.org/x/sync/errgroup"
)

func SolveDay02(ctx context.Context) (int, int, error) {
	g, ctx := errgroup.WithContext(ctx)

	lines, readFn := common.LinesFromFile(ctx, "day02.txt")
	g.Go(readFn)
	games, mapFn := common.MapValues(ctx, lines, parseCubeGameInput)
	g.Go(mapFn)
	var id int
	var sumOfIds int
	var sumOfPowers int
	g.Go(common.ForEach(ctx, games, func(_ context.Context, g cubeGameInput) error {
		id++
		if g.red <= 12 &&
			g.green <= 13 &&
			g.blue <= 14 {
			sumOfIds += id
		}
		sumOfPowers += int(g.red) * int(g.green) * int(g.blue)
		return nil
	}))

	return sumOfIds, sumOfPowers, g.Wait()
}

var cubeGameInputRegex = regexp.MustCompile(`\d+ [rgb]`)

func parseCubeGameInput(_ context.Context, line string) (
	result cubeGameInput,
	err error,
) {
	m := cubeGameInputRegex.FindAllString(line, -1)
	if len(m) == 0 {
		err = fmt.Errorf("parse error for line %q", line)
		return
	}
	var parsed int
	for _, v := range m {
		parsed, err = strconv.Atoi(v[:len(v)-2])
		if err != nil {
			return
		}
		p := uint8(parsed)
		var bucket *uint8
		switch v[len(v)-1] {
		case 'r':
			bucket = &result.red
		case 'g':
			bucket = &result.green
		case 'b':
			bucket = &result.blue
		}
		if p > *bucket {
			*bucket = p
		}
	}
	return
}

type cubeGameInput struct {
	red   uint8
	green uint8
	blue  uint8
}
