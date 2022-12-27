package problem19

import (
	"exercises/aoc2020/common"
	"fmt"
	"regexp"
	"strings"
)

func Solve() (int, int, error) {
	return SolveBoth("./problem19/input.txt")
}

func SolveBoth(inputFile string) (int, int, error) {
	lines, err := common.FileLines(inputFile)
	if err != nil {
		return 0, 0, err
	}
	rules, err := parseRules(lines)
	if err != nil {
		return 0, 0, err
	}
	count := 0
	for line := range lines {
		if rules.Match([]byte(line)) {
			count++
		}
	}
	return count, 0, nil
}

type rule struct {
	subrules [][]string
}

func parseRules(lines <-chan string) (*regexp.Regexp, error) {
	rules := map[string]rule{}
	for line := range lines {
		if len(line) == 0 {
			break
		}
		number, rule, err := parseRule(line)
		if err != nil {
			return nil, err
		}
		rules[number] = rule
	}
	return compileRuleZero(rules)
}

func compileRuleZero(rules map[string]rule) (*regexp.Regexp, error) {
	cache := map[string]string{}
	rule42, err := compileRule(rules, "42", cache)
	if err != nil {
		return nil, err
	}
	rule31, err := compileRule(rules, "31", cache)
	if err != nil {
		return nil, err
	}
	cache["8"] = fmt.Sprintf("%s+", rule42)
	var rule11 strings.Builder
	rule11.WriteRune('(')
	for i := 1; i < 5; i++ {
		if i > 1 {
			rule11.WriteRune('|')
		}
		for j := 0; j < i; j++ {
			rule11.WriteString(rule42)
		}
		for j := 0; j < i; j++ {
			rule11.WriteString(rule31)
		}
	}
	rule11.WriteRune(')')
	cache["11"] = rule11.String()
	ruleString, err := compileRule(rules, "0", cache)
	if err != nil {
		return nil, err
	}
	var sb strings.Builder
	sb.WriteRune('^')
	sb.WriteString(ruleString)
	sb.WriteRune('$')
	return regexp.Compile(sb.String())
}

func compileRule(rules map[string]rule, ruleName string, cache map[string]string) (string, error) {
	if value, exists := cache[ruleName]; exists {
		return value, nil
	}
	ruleString, err := computeRule(rules, ruleName, cache)
	if err != nil {
		return "", err
	}
	cache[ruleName] = ruleString
	return ruleString, nil
}

func computeRule(rules map[string]rule, ruleName string, cache map[string]string) (string, error) {
	rule, exists := rules[ruleName]
	if !exists {
		return "", fmt.Errorf("can't find rule %s", ruleName)
	}
	if rule.subrules[0][0][0] == '"' {
		str := rule.subrules[0][0]
		return str[1 : len(str)-1], nil
	}
	combined := len(rule.subrules) > 1
	var sb strings.Builder
	if combined {
		sb.WriteRune('(')
	}
	for i, ruleSequence := range rule.subrules {
		if i > 0 {
			sb.WriteRune('|')
		}
		for _, rule := range ruleSequence {
			ruleString, err := compileRule(rules, rule, cache)
			if err != nil {
				return "", err
			}
			sb.WriteString(ruleString)
		}
	}
	if combined {
		sb.WriteRune(')')
	}
	return sb.String(), nil
}

var ruleRe = regexp.MustCompile(`".+"|\d+|\|`)

func parseRule(line string) (string, rule, error) {
	parsed := ruleRe.FindAllStringSubmatch(line, -1)
	name := parsed[0][0]
	subrules := [][]string{{}}
	for i := 1; i < len(parsed); i++ {
		value := parsed[i][0]
		if value == "|" {
			subrules = append(subrules, []string{})
		} else {
			subrules[len(subrules)-1] = append(subrules[len(subrules)-1], value)
		}
	}
	return name, rule{subrules: subrules}, nil
}
