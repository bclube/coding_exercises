package problem04

import (
	"exercises/aoc2020/common"
	"regexp"
	"strconv"
)

func Solve() (int, int, error) {
	inputFile := "./problem04/input.txt"
	resultA, resultB, err := SolveBoth(inputFile)
	if err != nil {
		return 0, 0, err
	}
	return resultA, resultB, nil
}

func SolveBoth(inputFile string) (int, int, error) {
	records, err := parseFile(inputFile)
	if err != nil {
		return 0, 0, err
	}
	valid_a := 0
	valid_b := 0
	for record := range records {
		if is_valid_a(record) {
			valid_a++
			if is_valid_b(record) {
				valid_b++
			}
		}
	}
	return valid_a, valid_b, nil
}

func is_valid_a(passport map[string]string) bool {
	if len(passport) == 8 {
		return true
	}
	if len(passport) == 7 {
		_, exists := passport["cid"]
		return !exists
	}
	return false
}

func is_valid_b(passport map[string]string) bool {
	return validate_year(passport, "byr", 1920, 2002) &&
		validate_year(passport, "iyr", 2010, 2020) &&
		validate_year(passport, "eyr", 2020, 2030) &&
		valid_height(passport) &&
		validate_re(passport, "hcl", hairColorRe) &&
		validate_re(passport, "ecl", eyeColorRe) &&
		validate_re(passport, "pid", passportIdRe)
}

func validate_year(passport map[string]string, key string, min_year, max_year int) bool {
	year, exists := passport[key]
	if !exists {
		return false
	}
	value, err := strconv.Atoi(year)
	if err != nil {
		return false
	}
	return value >= min_year && value <= max_year
}

var heightRe = regexp.MustCompile(`(\d+)(in|cm)`)

func valid_height(passport map[string]string) bool {
	value, exists := passport["hgt"]
	if !exists {
		return false
	}
	matches := heightRe.FindStringSubmatch(value)
	if len(matches) != 3 {
		return false
	}
	amount, err := strconv.Atoi(matches[1])
	if err != nil {
		return false
	}
	if matches[2] == "cm" {
		return amount >= 150 && amount <= 193
	}
	if matches[2] == "in" {
		return amount >= 59 && amount <= 76
	}
	return false
}

var hairColorRe = regexp.MustCompile(`^#[0-9a-f]{6}$`)
var eyeColorRe = regexp.MustCompile(`^(amb|blu|brn|gry|grn|hzl|oth)$`)
var passportIdRe = regexp.MustCompile(`^\d{9}$`)

func validate_re(passport map[string]string, key string, re *regexp.Regexp) bool {
	value, exists := passport[key]
	return exists &&
		re.MatchString(value)
}

var batchFieldRe = regexp.MustCompile(`(\S+)?:(\S+)`)

func parseFile(inputFile string) (<-chan map[string]string, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return nil, err
	}
	out := make(chan map[string]string)
	go func() {
		defer close(out)
		current_batch := make(map[string]string)
		for line := range lines {
			matches := batchFieldRe.FindAllStringSubmatch(line, -1)
			if len(matches) == 0 && len(current_batch) > 0 {
				out <- current_batch
				current_batch = make(map[string]string)
			} else {
				for _, match := range matches {
					current_batch[match[1]] = match[2]
				}
			}
		}
		if len(current_batch) > 0 {
			out <- current_batch
		}
	}()
	return out, nil
}
