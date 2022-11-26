package problem07

import (
	"exercises/aoc2020/common"
	"regexp"
	"strconv"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem07/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	relations, err := parseFile(inputFile)
	if err != nil {
		return 0, 0, err
	}
	contained_by := map[string][]string{}
	contains := map[string][]relation{}
	for rel := range relations {
		if existing, exists := contained_by[rel.containedBag]; exists {
			existing = append(existing, rel.outer_bag)
			contained_by[rel.containedBag] = existing
		} else {
			contained_by[rel.containedBag] = []string{rel.outer_bag}
		}
		if existing, exists := contains[rel.outer_bag]; exists {
			existing = append(existing, rel)
			contains[rel.outer_bag] = existing
		} else {
			contains[rel.outer_bag] = []relation{rel}
		}
	}
	solutionAResults := map[string]bool{}
	countContainingBags(contained_by, solutionAResults, "shiny gold")
	solutionB := countBagsContainedBy(contains, "shiny gold") - 1
	return len(solutionAResults), solutionB, nil
}

func countBagsContainedBy(contains map[string][]relation, bag_name string) int {
	sum := 1
	for _, contained_bag := range contains[bag_name] {
		sum += contained_bag.quantity *
			countBagsContainedBy(contains, contained_bag.containedBag)
	}
	return sum
}

func countContainingBags(graph map[string][]string, results map[string]bool, bag_name string) {
	for _, containing_bag := range graph[bag_name] {
		if _, exists := results[containing_bag]; !exists {
			results[containing_bag] = true
			countContainingBags(graph, results, containing_bag)
		}
	}
}

type relation struct {
	outer_bag    string
	quantity     int
	containedBag string
}

var fileLineRe = regexp.MustCompile(`(\d+)? ?(\S+ \S+) bags?`)

func parseFile(inputFile string) (<-chan relation, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return nil, err
	}
	out := make(chan relation)
	go func() {
		defer close(out)
		for line := range lines {
			matches := fileLineRe.FindAllStringSubmatch(line, -1)
			outer_bag := matches[0][2]
			for _, match := range matches[1:] {
				if match[0] == " no other bags" {
					break
				}
				quantity, err := strconv.Atoi(match[1])
				if err != nil {
					panic(err)
				}
				out <- relation{
					outer_bag:    outer_bag,
					quantity:     quantity,
					containedBag: match[2],
				}
			}
		}
	}()
	return out, nil
}
