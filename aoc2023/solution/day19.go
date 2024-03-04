package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
	"strconv"
	"strings"
)

func SolveDay19(ctx context.Context) (int, error) {
	lines, err := common.ReadAllLines(ctx, "day19.txt")
	if err != nil {
		return 0, err
	}
	var line string
	workflows := make(map[string]partSortingWorkflow, len(lines))
	for _, line = range lines {
		if line == "" {
			break
		}
		name, flow, err := ParseWorkflow(line)
		if err != nil {
			return 0, err
		}
		workflows[name] = flow
	}
	acceptedCombinations, err := countAcceptedBranchCombinations(ctx, "in", workflows, maxWorkflowStep)
	if err != nil {
		return 0, err
	}
	return acceptedCombinations, nil
}

func countAcceptedBranchCombinations(ctx context.Context, workflow string, workflows map[string]partSortingWorkflow, partSpace workflowStep) (int, error) {
	if ctx.Err() != nil {
		return 0, ctx.Err()
	}
	if _, ok := workflows[workflow]; !ok {
		return 0, fmt.Errorf("workflow not found: %#v", workflow)
	}
	var result int
	excluded := partSpace
	for _, step := range workflows[workflow] {
		var included workflowStep
		included, excluded = processWorkflowStep(ctx, step, excluded)
		for _, parts := range []workflowStep{included, excluded} {
			switch {
			case parts.isEmpty(), parts.rejected:
				continue
			case parts.accepted:
				result += parts.acceptedCombinations()
			case parts.gotoStep != "":
				combinations, err := countAcceptedBranchCombinations(ctx, parts.gotoStep, workflows, parts)
				if err != nil {
					return 0, err
				}
				result += combinations
			}
		}
	}
	return result, nil
}

func processWorkflowStep(ctx context.Context, step workflowStep, partSpace workflowStep) (workflowStep, workflowStep) {
	included := step
	included.partRange = partSpace.partRange
	excluded := workflowStep{}
	excluded.partRange = partSpace.partRange
	for part := partCategoryX; part < __maxPartIndex__; part++ {
		if step.min[part] == 0 {
			continue
		}
		included.min[part] = max(partSpace.min[part], step.min[part])
		included.max[part] = min(partSpace.max[part], step.max[part])
		if step.min[part] == 1 {
			excluded.min[part] = max(included.max[part], partSpace.min[part])
		} else {
			excluded.max[part] = min(included.min[part], partSpace.max[part])
		}
	}
	return included, excluded
}

func ParseWorkflow(line string) (string, partSortingWorkflow, error) {
	split := strings.Split(line, "{")
	if len(split) != 2 {
		return "", nil, fmt.Errorf("invalid workflow: %s", line)
	}
	name := split[0]
	workflow := strings.TrimRight(split[1], "}")
	steps := strings.Split(workflow, ",")
	parsedSteps := make(partSortingWorkflow, len(steps))
	for i, step := range steps {
		var err error
		parsedSteps[i], err = ParseWorkflowStep(step)
		if err != nil {
			return "", nil, err
		}
	}
	return name, parsedSteps, nil
}

func ParseWorkflowStep(step string) (workflowStep, error) {
	split := strings.Split(step, ":")
	result := workflowStep{}
	switch s := split[len(split)-1]; s {
	case "A":
		result.accepted = true
	case "R":
		result.rejected = true
	default:
		result.gotoStep = s
	}
	if len(split) == 1 {
		result.partRange = maxWorkflowStep.partRange
		return result, nil
	}
	ptr := &result.max
	var diff int
	switch split[0][1] {
	case '<':
	case '>':
		diff = 1
		ptr = &result.min
	default:
		return workflowStep{}, fmt.Errorf("invalid step: %s", step)
	}
	partIndex := partCategoryX
	switch split[0][0] {
	case 'x':
	case 'm':
		partIndex = partCategoryM
	case 'a':
		partIndex = partCategoryA
	case 's':
		partIndex = partCategoryS
	default:
		return workflowStep{}, fmt.Errorf("invalid step: %s", step)
	}
	v, err := strconv.Atoi(split[0][2:])
	if err != nil {
		return workflowStep{}, err
	}
	result.min[partIndex] = 1
	result.max[partIndex] = 4001
	(*ptr)[partIndex] = v + diff
	return result, nil
}

var maxWorkflowStep = workflowStep{
	partRange: partRange{
		min: [__maxPartIndex__]int{1, 1, 1, 1},
		max: [__maxPartIndex__]int{4001, 4001, 4001, 4001},
	},
}

type machinePartCategory int

const (
	partCategoryX machinePartCategory = iota
	partCategoryM
	partCategoryA
	partCategoryS

	__maxPartIndex__
)

type partRange struct {
	min [__maxPartIndex__]int
	max [__maxPartIndex__]int
}

type workflowStep struct {
	partRange
	accepted, rejected bool
	gotoStep           string
}

func (ws *workflowStep) isEmpty() bool {
	for i := range ws.min {
		if ws.min[i] >= ws.max[i] {
			return true
		}
	}
	return false
}

func (ws *workflowStep) acceptedCombinations() int {
	result := 1
	for i := range ws.min {
		diff := ws.max[i] - ws.min[i]
		if diff <= 0 {
			return 0
		}
		result *= diff
	}
	return result
}

type partSortingWorkflow []workflowStep
