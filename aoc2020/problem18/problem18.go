package problem18

import (
	"exercises/aoc2020/common"
	"fmt"
	"regexp"
	"strconv"
)

func Solve() (int, error) {
	return SolveBoth("./problem18/input.txt")
}

func SolveBoth(inputFile string) (int, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return 0, err
	}
	sum := 0
	for line := range lines {
		result, err := Compute(line)
		if err != nil {
			return 0, err
		}
		sum += result
	}
	return sum, nil
}

const (
	lParen = iota
	rParen
	add
	multiply
	number
)

type token struct {
	tokenType int
	value     int
}

var tokenRe = regexp.MustCompile(`[+*()]|[0-9]+`)

func Compute(line string) (int, error) {
	tokens, err := parseLine(line)
	if err != nil {
		return 0, err
	}
	solution, _, err := computeMultiplication(tokens, 0)
	if err != nil {
		return 0, err
	}
	return solution, err
}

func parseLine(line string) ([]token, error) {
	results := tokenRe.FindAllStringSubmatch(line, -1)
	tokens := make([]token, 0, len(results))
	for _, v := range results {
		parsed := token{}
		switch v[0] {
		case "(":
			parsed.tokenType = lParen
		case ")":
			parsed.tokenType = rParen
		case "+":
			parsed.tokenType = add
		case "*":
			parsed.tokenType = multiply
		default:
			value, err := strconv.Atoi(v[0])
			if err != nil {
				return nil, err
			}
			parsed.tokenType = number
			parsed.value = value
		}
		tokens = append(tokens, parsed)
	}
	return tokens, nil
}

func consume(problem []token, index, expectedToken int) (bool, int) {
	if index < len(problem) && problem[index].tokenType == expectedToken {
		return true, index + 1
	}
	return false, index
}

func computeMultiplication(problem []token, index int) (int, int, error) {
	var newIndex int
	var err error
	left, newIndex, err := computeAddition(problem, index)
	if err != nil {
		return 0, 0, err
	}
	for {
		isMultiplication, nIndex := consume(problem, newIndex, multiply)
		if !isMultiplication {
			return left, nIndex, nil
		}
		var right int
		right, newIndex, err = computeAddition(problem, nIndex)
		if err != nil {
			return 0, 0, err
		}
		left *= right
	}
}

func computeAddition(problem []token, index int) (int, int, error) {
	var newIndex int
	var err error
	left, newIndex, err := getValue(problem, index)
	if err != nil {
		return 0, 0, err
	}
	for {
		isAddition, nIndex := consume(problem, newIndex, add)
		if !isAddition {
			return left, nIndex, nil
		}
		var right int
		right, newIndex, err = getValue(problem, nIndex)
		if err != nil {
			return 0, 0, err
		}
		left += right
	}
}

func getValue(problem []token, index int) (int, int, error) {
	if isLParen, newIndex := consume(problem, index, lParen); isLParen {
		left, newIndex, err := computeMultiplication(problem, newIndex)
		if err != nil {
			return 0, 0, err
		}
		if isRParen, newIndex := consume(problem, newIndex, rParen); isRParen {
			return left, newIndex, nil
		}
		return 0, 0, fmt.Errorf("expected ')'")
	}
	if index < len(problem) && problem[index].tokenType == number {
		return problem[index].value, index + 1, nil
	}
	return 0, 0, fmt.Errorf("expected '(' or number")
}
