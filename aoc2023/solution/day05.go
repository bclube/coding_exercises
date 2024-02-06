package solution

import (
	"aoc2023/common"
	"context"
	"math"
	"strconv"
	"strings"
)

func SolveDay05(ctx context.Context) (int, error) {
	lines, err := common.ReadAllLines(ctx, "day05.txt")
	if err != nil {
		return 0, err
	}
	var i int
	resources := getSeeds(lines, &i)
	for n := 0; n < 7; n++ {
		resourceMaps := getMap(lines, &i)
		mappedResources := make([]resourceRange, 0, len(resources)*5)
		for _, resource := range resources {
			mappedResources = mapToDestination(ctx, resourceMaps, resource, mappedResources)
		}
		resources = mappedResources
	}
	min := math.MaxInt
	for _, resource := range resources {
		if resource.begin < min {
			min = resource.begin
		}
	}
	return min, nil
}

func mapToDestination(ctx context.Context, resourceMaps []resourceMap, source resourceRange, to []resourceRange) (
	mapped []resourceRange,
) {
	mapped = to
	for i, resourceMap := range resourceMaps {
		select {
		case <-ctx.Done():
			return nil
		default:
		}

		if source.end <= resourceMap.begin || source.begin >= resourceMap.end {
			continue
		}

		if source.begin < resourceMap.begin {
			split := resourceRange{source.begin, resourceMap.begin}
			source.begin = resourceMap.begin
			mapped = mapToDestination(ctx, resourceMaps[i+1:], split, mapped)
		}

		if source.end > resourceMap.end {
			split := resourceRange{resourceMap.end, source.end}
			source.end = resourceMap.end
			mapped = mapToDestination(ctx, resourceMaps[i+1:], split, mapped)
		}

		source.begin += resourceMap.diff
		source.end += resourceMap.diff

		return append(mapped, source)

	}
	return append(mapped, source)
}

func getSeeds(lines []string, i *int) []resourceRange {
	seeds := make([]resourceRange, 0, 10)
	for *i++; *i < len(lines); *i++ {
		if lines[*i] == "" {
			break
		}
		parts := strings.Split(lines[*i], " ")
		from, _ := strconv.Atoi(parts[0])
		length, _ := strconv.Atoi(parts[1])
		seeds = append(seeds, resourceRange{
			begin: from,
			end:   from + length,
		})
	}
	return seeds
}

func getMap(lines []string, i *int) []resourceMap {
	result := make([]resourceMap, 0, 50)
	for *i += 2; *i < len(lines); *i++ {
		if lines[*i] == "" {
			break
		}
		parts := strings.Split(lines[*i], " ")
		dest, _ := strconv.Atoi(parts[0])
		source, _ := strconv.Atoi(parts[1])
		length, _ := strconv.Atoi(parts[2])
		result = append(result, resourceMap{
			begin: source,
			end:   source + length,
			diff:  dest - source,
		})
	}
	return result
}

type resourceRange struct {
	begin int
	end   int
}

type resourceMap struct {
	begin int
	end   int
	diff  int
}
