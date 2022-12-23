package problem16

import (
	"exercises/aoc2020/common"
	"fmt"
	"regexp"
	"strconv"
	"strings"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem16/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	ticketData, err := parseFile(inputFile)
	if err != nil {
		return 0, 0, err
	}
	solutionA := 0
	first := true
	possiblities := []map[string]bool{}
	// TODO: this could use some refactoring for clarity
	for _, nearbyTicket := range ticketData.nearbyTickets {
		mismatchedField, possibleFields := validateTicket(ticketData.fields, nearbyTicket)
		solutionA += mismatchedField
		if len(possibleFields) > 0 {
			if first {
				possiblities = possibleFields
				first = false
			} else {
				for i := 0; i < len(possiblities); i++ {
					intersection := map[string]bool{}
					for field := range possibleFields[i] {
						if _, exists := possiblities[i][field]; exists {
							intersection[field] = true
						}
					}
					possiblities[i] = intersection
				}
			}
		}
	}
	fields := findFieldNames(possiblities)
	solutionB := 1
	for i := 0; i < len(fields); i++ {
		if strings.HasPrefix(fields[i], "departure") {
			solutionB *= ticketData.yourTicket[i]
		}
	}
	return solutionA, solutionB, nil
}

func findFieldNames(possiblities []map[string]bool) []string {
	solved := map[int]string{}
	lookup := map[string]bool{}
	for len(solved) < len(possiblities) {
		for i, possibility := range possiblities {
			if _, alreadySolved := solved[i]; alreadySolved {
				continue
			}
			if len(possibility) <= len(solved)+1 {
				for k := range possibility {
					if lookup[k] {
						continue
					}
					solved[i] = k
					lookup[k] = true
				}
			}
		}
	}
	result := make([]string, len(solved))
	for i, field := range solved {
		result[i] = field
	}
	return result
}

func validateTicket(ticketFields map[string][]validRange, nearbyTicket []int) (int, []map[string]bool) {
	possibleFields := []map[string]bool{}
	for _, ticketValue := range nearbyTicket {
		fields := validFields(ticketFields, ticketValue)
		if len(fields) == 0 {
			return ticketValue, nil
		}
		possibleFields = append(possibleFields, fields)
	}
	return 0, possibleFields
}

func validFields(ticketFields map[string][]validRange, ticketValue int) map[string]bool {
	result := map[string]bool{}
	for fieldName, validRanges := range ticketFields {
		for _, validRange := range validRanges {
			if ticketValue >= validRange.low && ticketValue <= validRange.high {
				result[fieldName] = true
			}
		}
	}
	return result
}

type validRange struct {
	low  int
	high int
}

type ticketData struct {
	fields        map[string][]validRange
	yourTicket    []int
	nearbyTickets [][]int
}

func parseFile(inputFile string) (ticketData, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return ticketData{}, err
	}
	fields := map[string][]validRange{}
	for line := range lines {
		if len(line) == 0 {
			break
		}
		fieldName, ranges, err := parseField(line)
		if err != nil {
			return ticketData{}, err
		}
		fields[fieldName] = ranges
	}
	line := <-lines
	if line != "your ticket:" {
		return ticketData{}, fmt.Errorf("expected \"your ticket:\"")
	}
	yourTicket, err := parseTicket(<-lines)
	if err != nil {
		return ticketData{}, err
	}
	<-lines // a blank line
	line = <-lines
	if line != "nearby tickets:" {
		return ticketData{}, fmt.Errorf("expected \"nearby tickets:\"")
	}
	nearbyTickets := [][]int{}
	for nearbyTicketLine := range lines {
		nearbyTicket, err := parseTicket(nearbyTicketLine)
		if err != nil {
			return ticketData{}, err
		}
		nearbyTickets = append(nearbyTickets, nearbyTicket)
	}
	result := ticketData{
		fields:        fields,
		yourTicket:    yourTicket,
		nearbyTickets: nearbyTickets,
	}
	return result, nil
}

var ticketRe = regexp.MustCompile(`(\d+)`)

func parseTicket(line string) ([]int, error) {
	ticketValues := ticketRe.FindAllStringSubmatch(line, -1)
	if len(ticketValues) == 0 {
		return nil, fmt.Errorf("unable to parse ticket")
	}
	result := make([]int, 0, len(ticketValues))
	for _, t := range ticketValues {
		parsed, err := strconv.Atoi(t[0])
		if err != nil {
			return nil, err
		}
		result = append(result, parsed)
	}
	return result, nil
}

var fieldRe = regexp.MustCompile(`^(.+?): (\d+)-(\d+) or (\d+)-(\d+)$`)

func parseField(line string) (string, []validRange, error) {
	parsed := fieldRe.FindStringSubmatch(line)
	ints := make([]int, 0, 4)
	for i := 2; i < 6; i++ {
		v, err := strconv.Atoi(parsed[i])
		if err != nil {
			return "", nil, err
		}
		ints = append(ints, v)
	}
	ranges := []validRange{
		{low: ints[0], high: ints[1]},
		{low: ints[2], high: ints[3]},
	}
	return parsed[1], ranges, nil
}
