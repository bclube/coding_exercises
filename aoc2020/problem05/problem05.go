package problem05

import (
	"exercises/aoc2020/common"
	"sort"
)

func Solve() (int, int, error) {
	lines, err := common.ParseFile("./problem05/input.txt", FindSeatId)
	if err != nil {
		return 0, 0, err
	}
	seat_ids := []int{}
	for line := range lines {
		seat_ids = append(seat_ids, line)
	}
	sort.Ints(seat_ids)
	highest := seat_ids[len(seat_ids)-1]
	last_seat := seat_ids[0] - 1
	for _, seat_id := range seat_ids {
		last_seat++
		if seat_id != last_seat {
			break
		}
	}
	return highest, last_seat, nil
}

func FindSeatId(boardingPass string) (int, error) {
	result := 0
	for _, ch := range boardingPass {
		result = result << 1
		if ch == 'B' || ch == 'R' {
			result += 1
		}
	}
	return result, nil
}
