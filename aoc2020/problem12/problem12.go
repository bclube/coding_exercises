package problem12

import (
	"exercises/aoc2020/common"
	"regexp"
	"strconv"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem12/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	instructions, err := common.ParseFile(inputFile, parseInstruction)
	if err != nil {
		return 0, 0, err
	}
	x, y, d := 0, 0, "E"
	px, py, wx, wy := 0, 0, 10, 1
	for instruction := range instructions {
		x, y, d = followInstruction(instruction.action, instruction.amount, x, y, d)
		px, py, wx, wy = followInstructionB(instruction.action, instruction.amount, px, py, wx, wy)
	}
	solutionA := abs(x) + abs(y)
	solutionB := abs(px) + abs(py)
	return solutionA, solutionB, nil
}

func abs(v int) int {
	if v >= 0 {
		return v
	}
	return -v
}

func followInstruction(action string, amount int, x, y int, d string) (int, int, string) {
	switch action {
	case "N":
		return x, y + amount, d
	case "S":
		return x, y - amount, d
	case "E":
		return x + amount, y, d
	case "W":
		return x - amount, y, d
	case "R":
		if amount == 0 {
			return x, y, d
		}
		var nextDirection string
		switch d {
		case "N":
			nextDirection = "E"
		case "E":
			nextDirection = "S"
		case "S":
			nextDirection = "W"
		case "W":
			nextDirection = "N"
		}
		return followInstruction("R", amount-90, x, y, nextDirection)
	case "L":
		return followInstruction("R", 360-amount, x, y, d)
	case "F":
		return followInstruction(d, amount, x, y, d)
	default:
		panic("invalid action")
	}
}

func followInstructionB(action string, amount, px, py, wx, wy int) (int, int, int, int) {
	switch action {
	case "N":
		return px, py, wx, wy + amount
	case "S":
		return px, py, wx, wy - amount
	case "E":
		return px, py, wx + amount, wy
	case "W":
		return px, py, wx - amount, wy
	case "L":
		if amount == 0 {
			return px, py, wx, wy
		}
		return followInstructionB(action, amount-90, px, py, -wy, wx)
	case "R":
		return followInstructionB("L", 360-amount, px, py, wx, wy)
	case "F":
		return px + (wx * amount), py + (wy * amount), wx, wy
	default:
		panic("invalid action")
	}
}

type instruction struct {
	action string
	amount int
}

var instructionRe = regexp.MustCompile(`(.)(\d+)`)

func parseInstruction(line string) (instruction, error) {
	matches := instructionRe.FindStringSubmatch(line)
	amount, err := strconv.Atoi(matches[2])
	if err != nil {
		return instruction{}, err
	}
	result := instruction{
		action: matches[1],
		amount: amount,
	}
	return result, nil
}
