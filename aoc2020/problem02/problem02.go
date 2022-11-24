package problem02

import (
	"exercises/aoc2020/common"
	"regexp"
	"strconv"
)

func Solve() (int, int, error) {
	inputFile := "./problem02/input.txt"
	resultA, resultB, err := SolveBoth(inputFile)
	if err != nil {
		return 0, 0, err
	}
	return resultA, resultB, nil
}

func SolveBoth(inputFile string) (int, int, error) {
	input, err := common.ParseFile(inputFile, parseLine)
	if err != nil {
		return 0, 0, err
	}
	validCountA, validCountB := 0, 0
	for password := range input {
		if password.is_valid() {
			validCountA++
		}
		if password.is_valid_b() {
			validCountB++
		}
	}
	return validCountA, validCountB, nil
}

type PasswordData struct {
	RangeBegin int
	RangeEnd   int
	Letter     byte
	Password   string
}

func (pd *PasswordData) is_valid() bool {
	count := 0
	for _, c := range pd.Password {
		if c == rune(pd.Letter) {
			count++
		}
	}
	return count >= pd.RangeBegin && count <= pd.RangeEnd
}

func (pd *PasswordData) is_valid_b() bool {
	matchFirst := pd.Password[pd.RangeBegin-1] == pd.Letter
	matchSecond := pd.Password[pd.RangeEnd-1] == pd.Letter
	return matchFirst != matchSecond // xor
}

var inputRe = regexp.MustCompile(`^(\d+)-(\d+) (.): (.*)$`)

func parseLine(line string) (PasswordData, error) {
	matches := inputRe.FindStringSubmatch(line)
	rangeBegin, err := strconv.Atoi(matches[1])
	if err != nil {
		return PasswordData{}, err
	}
	rangeEnd, err := strconv.Atoi(matches[2])
	if err != nil {
		return PasswordData{}, err
	}
	letter := matches[3][0]
	password := matches[4]
	result := PasswordData{
		RangeBegin: rangeBegin,
		RangeEnd:   rangeEnd,
		Letter:     letter,
		Password:   password,
	}
	return result, nil
}
