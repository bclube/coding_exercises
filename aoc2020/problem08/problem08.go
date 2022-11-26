package problem08

import (
	"errors"
	"exercises/aoc2020/common"
	"fmt"
	"regexp"
	"strconv"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem08/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	instructions, err := common.ParseFile(inputFile, parseLine)
	if err != nil {
		return 0, 0, err
	}
	program := []machineInstruction{}
	for instruction := range instructions {
		program = append(program, instruction)
	}
	solutionA, _ := run(program)
	solutionB, err := solveB(program)
	return solutionA, solutionB, err
}

func solveB(program []machineInstruction) (int, error) {
	for i := range program {
		if swapInstruction(program, i) {
			if result, terminated := run(program); terminated {
				return result, nil
			}
			swapInstruction(program, i)
		}
	}
	return 0, errors.New("unable to find solution")
}

func swapInstruction(program []machineInstruction, i int) bool {
	op := &program[i]
	switch op.op {
	case jmp:
		op.op = nop
		return true
	case nop:
		op.op = jmp
		return true
	default:
		return false
	}
}

func run(program []machineInstruction) (int, bool) {
	instruction := 0
	accumulator := 0
	visited := map[int]bool{}
	for {
		if _, already_visited := visited[instruction]; already_visited {
			return accumulator, false
		}
		if instruction == len(program) {
			return accumulator, true
		}
		visited[instruction] = true
		v := program[instruction]
		instruction++
		switch v.op {
		case acc:
			accumulator += v.quantity
		case jmp:
			instruction += v.quantity - 1
		}
	}
}

type opCode byte

const (
	nop opCode = iota
	acc
	jmp
)

type machineInstruction struct {
	op       opCode
	quantity int
}

var machineInstructionRe = regexp.MustCompile(`^(\S+?) ([-+]\d+)$`)

func parseLine(line string) (machineInstruction, error) {
	matches := machineInstructionRe.FindStringSubmatch(line)
	if len(matches) != 3 {
		return machineInstruction{}, fmt.Errorf("could not parse instruction %q", line)
	}
	var op opCode
	switch matches[1] {
	case "nop":
		op = nop
	case "acc":
		op = acc
	case "jmp":
		op = jmp
	default:
		return machineInstruction{}, fmt.Errorf("invalid op code %q", matches[1])
	}
	quantity, err := strconv.Atoi(matches[2])
	if err != nil {
		return machineInstruction{}, err
	}
	return machineInstruction{
		op:       op,
		quantity: quantity,
	}, nil
}
