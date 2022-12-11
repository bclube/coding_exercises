package problem13

import (
	"exercises/aoc2020/common"
	"math"
	"regexp"
	"strconv"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem13/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	earliestDeparture, schedule, err := parseFile(inputFile)
	if err != nil {
		return 0, 0, err
	}
	solutionA := solveA(earliestDeparture, schedule)
	solutionB := SolveB(schedule)
	return solutionA, solutionB, nil
}

func solveA(earliestDeparture int, schedule []int) int {
	first := true
	var min int
	var minBus int
	for _, busId := range schedule {
		if busId == -1 {
			continue
		}
		solution := departureTime(earliestDeparture, busId)
		if first || solution < min {
			min = solution
			minBus = busId
		}
		first = false
	}
	return (min - earliestDeparture) * minBus
}

func departureTime(earliestDeparture, busId int) int {
	cycles := math.Ceil(float64(earliestDeparture) / float64(busId))
	return int(cycles) * busId
}

func SolveB(schedule []int) int {
	time := 0
	cycleLength := 1
	first := true
	for offset, busId := range schedule {
		if busId == -1 {
			continue
		}
		if first {
			cycleLength = busId
			first = false
			continue
		}
		for {
			solution := departureTime(time+offset, busId)
			if solution-time == offset {
				cycleLength *= busId
				break
			}
			time += cycleLength
		}
	}
	return time
}

var busScheduleRe = regexp.MustCompile(`(x|\d+)`)

func parseFile(inputFile string) (int, []int, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return 0, nil, err
	}
	earliestDeparture, err := strconv.Atoi(<-lines)
	if err != nil {
		return 0, nil, err
	}
	matches := busScheduleRe.FindAllStringSubmatch(<-lines, -1)
	schedule := []int{}
	for _, match := range matches {
		parsed, err := parseScheduleEntry(match[0])
		if err != nil {
			return 0, nil, err
		}
		schedule = append(schedule, parsed)
	}
	return earliestDeparture, schedule, nil
}

func parseScheduleEntry(entry string) (int, error) {
	if entry == "x" {
		return -1, nil
	}
	return strconv.Atoi(entry)
}
