package problem14

import (
	"exercises/aoc2020/common"
	"fmt"
	"math"
	"regexp"
	"strconv"
)

func Solve() (uint64, uint64, error) {
	return SolveBoth("./problem14/input.txt")
}

func SolveBoth(inputFile string) (uint64, uint64, error) {
	instructions, err := common.ParseFile(inputFile, parseLine)
	if err != nil {
		return 0, 0, err
	}
	maskOnes, maskZeros := uint64(0), uint64(math.MaxUint64)
	maskXs := []uint64{}
	memoryA := map[uint64]uint64{}
	memoryB := map[uint64]uint64{}
	for instr := range instructions {
		switch instr.instructionType {
		case mask:
			maskOnes = instr.ones
			maskZeros = instr.zeros
			maskXs = instr.xs
		case mem:
			valueA := (instr.value | maskOnes) & (maskZeros ^ math.MaxUint64)
			memoryA[instr.address] = valueA
			addressB := (instr.address & maskZeros) | maskOnes
			setMemoryAddresses(memoryB, maskXs, addressB, instr.value)
		}
	}
	solutionA := uint64(0)
	for _, v := range memoryA {
		solutionA += v
	}
	solutionB := uint64(0)
	for _, v := range memoryB {
		solutionB += v
	}
	return solutionA, solutionB, nil
}

func setMemoryAddresses(memoryB map[uint64]uint64, maskXs []uint64, addressB, value uint64) {
	if len(maskXs) == 0 {
		memoryB[addressB] = value
		return
	}
	setMemoryAddresses(memoryB, maskXs[1:], addressB, value)
	addressB ^= maskXs[0]
	setMemoryAddresses(memoryB, maskXs[1:], addressB, value)
}

const (
	mask = iota
	mem
)

type instruction struct {
	instructionType int
	address         uint64
	value           uint64
	ones            uint64
	zeros           uint64
	xs              []uint64
}

var maskRe = regexp.MustCompile(`^mask = ([X01]{36})$`)
var memRe = regexp.MustCompile(`^mem\[(\d+)] = (\d+)$`)

func parseLine(line string) (instruction, error) {
	matches := maskRe.FindStringSubmatch(line)
	if len(matches) > 0 {
		ones, zeros, xs := parseBitMask(matches[1])
		result := instruction{
			instructionType: mask,
			ones:            ones,
			zeros:           zeros,
			xs:              xs,
		}
		return result, nil
	}
	matches2 := memRe.FindStringSubmatch(line)
	if len(matches2) > 0 {
		address, err := strconv.ParseUint(matches2[1], 10, 64)
		if err != nil {
			return instruction{}, err
		}
		value, err := strconv.ParseUint(matches2[2], 10, 64)
		if err != nil {
			return instruction{}, err
		}
		result := instruction{
			instructionType: mem,
			address:         address,
			value:           value,
		}
		return result, nil
	}
	return instruction{}, fmt.Errorf("unable to parse line: \"%q\"", line)
}

func parseBitMask(bitmask string) (uint64, uint64, []uint64) {
	ones, zeros := uint64(0), uint64(0)
	xs := []uint64{}
	length := len(bitmask)
	for i, c := range bitmask {
		switch c {
		case '1':
			ones |= 1 << (length - i - 1)
		case '0':
			zeros |= 1 << (length - i - 1)
		case 'X':
			xs = append(xs, 1<<(length-i-1))
		}
	}
	return ones, zeros, xs
}
