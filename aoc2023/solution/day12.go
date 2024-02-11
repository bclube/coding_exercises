package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
	"strconv"
	"strings"

	"golang.org/x/sync/errgroup"
)

func SolveDay12(ctx context.Context) (int, error) {
	g, ctx := errgroup.WithContext(ctx)
	lines, lineReader := common.LinesFromFile(ctx, "day12.txt")
	g.Go(lineReader)
	var sum int
	g.Go(common.ForEach(ctx, lines, func(ctx context.Context, line string) error {
		validArrangements, err := CountValidArrangements(ctx, line)
		if err != nil {
			return err
		}
		sum += validArrangements
		return nil
	}))

	return sum, g.Wait()
}

func CountValidArrangements(ctx context.Context, line string) (int, error) {
	split := strings.Split(line, " ")
	if len(split) != 2 {
		return 0, fmt.Errorf("invalid line: %s", line)
	}
	conditionRecord := unfold(split[0], '?')

	ints := strings.Split(split[1], ",")
	groups := make([]int, len(ints)*5)
	for i, s := range ints {
		value, err := strconv.Atoi(s)
		if err != nil {
			return 0, fmt.Errorf("invalid line: %s", line)
		}
		for j := 0; j < 5; j++ {
			groups[j*len(ints)+i] = value
		}
	}
	solutionCache := springSolutionCache{}
	result := countValidPermutations(ctx, conditionRecord, groups, solutionCache)
	return result, nil
}

type springSolutionCacheKey struct {
	conditionSize int
	groupSize     int
}

type springSolutionCache map[springSolutionCacheKey]int

func unfold(folded string, join rune) string {
	var sb strings.Builder
	for i := 0; i < 5; i++ {
		if i > 0 {
			sb.WriteRune(join)
		}
		sb.WriteString(folded)
	}
	return sb.String()
}

func countValidPermutations(ctx context.Context, conditionRecord string, groups []int, cache springSolutionCache) (result int) {
	cacheKey := springSolutionCacheKey{
		conditionSize: len(conditionRecord),
		groupSize:     len(groups),
	}
	if cached, ok := cache[cacheKey]; ok {
		return cached
	}
	defer func() {
		cache[cacheKey] = result
	}()
	if len(groups) == 0 {
		for _, r := range conditionRecord {
			if r == damagedSpring {
				return 0
			}
		}
		return 1
	}
	for i, r := range conditionRecord {
		switch r {
		case damagedSpring:
			result += placeDamagedSprings(ctx, conditionRecord[i:], groups, cache)
			return
		case springWithUnknownStatus:
			result += placeDamagedSprings(ctx, conditionRecord[i:], groups, cache)
		}
	}
	return
}

func placeDamagedSprings(ctx context.Context, conditionRecord string, groups []int, cache springSolutionCache) int {
	springsInThisGroup := groups[0]
	if springsInThisGroup > len(conditionRecord) {
		return 0
	}
	for i := 0; i < springsInThisGroup; i++ {
		if conditionRecord[i] == operationalSpring {
			return 0
		}
	}
	next := ""
	if springsInThisGroup < len(conditionRecord) {
		if conditionRecord[springsInThisGroup] == damagedSpring {
			return 0
		}
		next = conditionRecord[springsInThisGroup+1:]
	}
	return countValidPermutations(ctx, next, groups[1:], cache)
}

const (
	damagedSpring           = '#'
	operationalSpring       = '.'
	springWithUnknownStatus = '?'
)
