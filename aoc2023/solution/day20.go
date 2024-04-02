package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
	"math"
	"slices"
	"strings"
)

const (
	countPulses = false
)

var (
	highPulseCount,
	lowPulseCount int
)

func SolveDay20(ctx context.Context) (int, error) {
	moduleIndex, err := parseModuleNetwork(ctx)
	if err != nil {
		return 0, err
	}
	printModuleNetwork(moduleIndex)
	/*
		I solved this on paper, but left a bit of the network simulation code here for illustration purposes.

		Observation of the provided input reveals that the module network is composed of four independent module networks.
		Each of these networks sends a single high pulse to the `jm` module on a set interval and then cycles back to its
		original state. Finding the least common multiple of the subnetwork cycle lengths gives the final answer.

		Here's one of the four subnetworks, edited and reordered for clarity:

		broadcaster -> mn
		%mn -> bc, hv
		%hv -> xb
		%xb -> zl
		%zl -> zh
		%zh -> bc, st
		%st -> bc, mm
		%mm -> gz
		%gz -> nf
		%nf -> bc, tg
		%tg -> bc, dx
		%dx -> bc, hk
		%hk -> bc
		&bc -> mn, zl, xb, mm, dh, hv, gz
		&dh -> jm
		&jm -> rx

		The broadcaster module feeds directly into the `mn` flip flop, and the output of `mn` feeds directly into another flip flop
		(`hv`) and so on down a chain of 12 flip flops in total. This essentially acts as a 12-bit binary counter. The `bc` conjunction
		will fire off a single low pulse when all of its inputs become `1`. Its inputs are all bits in the flip flop counter; i.e. it
		will fire when the counter reaches the value where each of the `bc` input bits is `1` and each of the non-input bits is `0`.

		1111 0011 0001 -> 3889

		At this point, `bc` will fire off a single low pulse. This low pulse flows through the `dh` inverter, sending a high pulse to
		`jm`. The low pulse from `bc` also resets all of the flip flops back to `0`, which restarts the subnetwork's cycle:

		1111 0011 0010
		1111 0011 1010
		1111 0011 1110
		1111 0111 1110
		0000 0000 0000

		A similar pattern occurs with the other three subnetworks, but each has a unique cycle length. Since each subnetwork emits a
		single high pulse to `jm` on a regular cycle, we can determine that they will sync up every time their cycles sync up. This
		is found by calculating the least common multiple of the cycle lengths. After this many cycles, each subnetwork will emit a high
		pulse to `jm` at the same time, resulting in a single low pulse being sent to `rx`.
	*/
	mnCycle, err := runModuleNetwork(ctx, moduleIndex)
	if err != nil {
		return 0, err
	}
	const plCycle = 3851
	const xcCycle = 4079
	const xrCycle = 4027
	return lcm(mnCycle, plCycle, xcCycle, xrCycle), nil
}

func printModuleNetwork(moduleIndex communicationModuleIndex) {
	modules := make([]*parsedCommunicationModule, 0, len(moduleIndex))
	for _, module := range moduleIndex {
		modules = append(modules, module)
	}
	slices.SortFunc(modules, func(i, j *parsedCommunicationModule) int {
		if i.moduleType != j.moduleType {
			return int(i.moduleType) - int(j.moduleType)
		}
		if len(i.inputModules) != len(j.inputModules) {
			return len(i.inputModules) - len(j.inputModules)
		}
		return i.id - j.id
	})
	for _, module := range modules {
		fmt.Print(module.moduleType, " ", module.name)
		var suffix string
		for i, in := range module.inputModules {
			if i == 0 {
				fmt.Print(" <-")
			}
			switch {
			case module.moduleType == untypedCommunicationModule:
				fmt.Print(" !")
				if in.moduleType == flipFlop {
					fmt.Print("%")
				}
				fmt.Print(in.name)
			case module.moduleType == flipFlop && len(module.inputModules) > 1:
				if i == 0 {
					fmt.Print(" !(")
					suffix = ")"
				} else {
					fmt.Print(" && ")
				}
				if in.moduleType == flipFlop {
					fmt.Print("%")
				}
				fmt.Print(in.name)
			case module.moduleType == flipFlop:
				fmt.Print(" !")
				if in.moduleType == flipFlop {
					fmt.Print("%")
				}
				fmt.Print(in.name)
			case module.moduleType == conjunction && len(module.inputModules) > 1:
				if i == 0 {
					fmt.Print(" !(")
					suffix = ")"
				} else {
					fmt.Print(" && ")
				}
				if in.moduleType == flipFlop {
					fmt.Print("%")
				}
				fmt.Print(in.name)
			default:
				fmt.Print(" !", in.name)
			}
		}
		fmt.Print(suffix)
		if module.moduleType == flipFlop {
			fmt.Print(" => ~", module.name)
		}
		for i, out := range module.outputModules {
			if i == 0 {
				fmt.Print(" ->")
			} else {
				fmt.Print(",")
			}
			fmt.Print(" ", out.name)
		}
		fmt.Println()
	}
}

type communicationModuleStep struct {
	mask            uint64
	sendersInterted uint64
	name            string
	sendLow         []uint8
	sendHigh        []uint8
	moduleType      communicationModuleType
	sendCount       uint8
}

func runModuleNetwork(ctx context.Context, moduleIndex communicationModuleIndex) (int, error) {
	broadcaster, ok := moduleIndex["broadcaster"]
	if !ok {
		return 0, fmt.Errorf("no broadcaster found")
	}
	var final *parsedCommunicationModule
	modules := make([]*parsedCommunicationModule, len(moduleIndex))
	for _, module := range moduleIndex {
		if module.moduleType == untypedCommunicationModule {
			final = module
		}
		modules[module.id] = module
	}
	if final == nil {
		return 0, fmt.Errorf("no final module found")
	}
	highIndex := make(map[int]int)
	for _, module := range modules {
		if module.moduleType == conjunction {
			highIndex[module.id] = len(highIndex) + len(modules)
		}
	}
	steps := make([]communicationModuleStep, len(highIndex)+len(modules))
	for i, module := range modules {
		steps[i].name = module.name
		steps[i].mask = module.mask
		steps[i].moduleType = module.moduleType
		steps[i].sendCount = uint8(len(module.outputModules))
		for _, out := range module.outputModules {
			if sendToHigh, ok := highIndex[out.id]; ok {
				steps[i].sendHigh = append(steps[i].sendHigh, uint8(sendToHigh))
			}
			if module.moduleType != conjunction {
				steps[i].sendLow = append(steps[i].sendLow, uint8(out.id))
			}
		}
		if highId, ok := highIndex[module.id]; ok {
			steps[highId].name = module.name
			steps[highId].mask = module.mask
			steps[highId].moduleType = module.moduleType
			steps[highId].sendCount = uint8(len(module.outputModules))
			steps[highId].sendersInterted = ^module.senders
			for _, out := range module.outputModules {
				if sendToHigh, ok := highIndex[out.id]; ok {
					steps[highId].sendHigh = append(steps[highId].sendHigh, uint8(sendToHigh))
				}
				steps[highId].sendLow = append(steps[highId].sendLow, uint8(out.id))
			}
		}
	}
	broacasterIndex := broadcaster.id
	broadcasterPulses := steps[broacasterIndex].sendCount + 1
	var state uint64
	pulses := append(
		make([][]uint8, 0, 200),
		steps[broacasterIndex].sendLow,
	)
	var iteration int
	for {
		if ctx.Err() != nil {
			return 0, ctx.Err()
		}
		if countPulses {
			go func(i, h, l int) { fmt.Println("iteration", i, h, l) }(iteration, highPulseCount, lowPulseCount)
		} else {
			go func(i int) { fmt.Println("iteration", i) }(iteration)
		}
		for i := 0; i < 1_000_000; i++ {
			iteration++
			queue := pulses
			if countPulses {
				lowPulseCount += int(broadcasterPulses)
			}
			for qIndex := 0; qIndex < len(queue); qIndex++ {
				if countPulses && qIndex > cap(pulses) {
					panic("queue cap exceeded")
				}
				q := queue[qIndex]
				for _, pulse := range q {
					step := steps[pulse]
					switch {
					case step.moduleType == conjunction &&
						step.sendersInterted != 0 &&
						(state|step.sendersInterted == math.MaxUint64):
						state &= ^step.mask
						if countPulses {
							lowPulseCount += int(step.sendCount)
						}
						if step.sendLow == nil {
							continue
						}
						queue = append(queue, step.sendLow)
					case step.moduleType == conjunction:
						state |= step.mask
						if countPulses {
							highPulseCount += int(step.sendCount)
						}
						if step.sendHigh == nil {
							continue
						}
						queue = append(queue, step.sendHigh)
					case step.moduleType == flipFlop && state&step.mask == 0:
						state |= step.mask
						if countPulses {
							highPulseCount += int(step.sendCount)
						}
						if step.sendHigh == nil {
							continue
						}
						queue = append(queue, step.sendHigh)
					case step.moduleType == flipFlop:
						state &= ^step.mask
						if countPulses {
							lowPulseCount += int(step.sendCount)
						}
						if step.sendLow == nil {
							continue
						}
						queue = append(queue, step.sendLow)
					case step.moduleType == untypedCommunicationModule:
						fmt.Println("done")
						return iteration, nil
					default:
						panic("should not be reachable")
					}
				}
			}
			if countPulses && iteration == 1_000 && highPulseCount*lowPulseCount != 841763884 {
				panic(fmt.Sprintf("highPulseCount %d lowPulseCount %d diff %d", highPulseCount, lowPulseCount, highPulseCount*lowPulseCount-841763884))
			}
		}
	}
}

func parseModuleNetwork(ctx context.Context) (
	communicationModuleIndex,
	error,
) {
	lines, err := common.ReadAllLines(ctx, "day20.txt")
	if err != nil {
		return nil, err
	}
	moduleIndex := make(communicationModuleIndex, len(lines))
	for _, line := range lines {
		module, err := parseCommunicationModule(line, moduleIndex)
		if err != nil {
			return nil, err
		}
		if module == nil {
			break
		}
	}
	return moduleIndex, nil
}

func parseCommunicationModule(line string, moduleIndex communicationModuleIndex) (*parsedCommunicationModule, error) {
	split := strings.Split(line, " -> ")
	if len(split) != 2 {
		return nil, nil
	}
	outputModules := strings.Split(split[1], ", ")
	if len(outputModules) == 0 {
		return nil, fmt.Errorf("no output modules: %#v", split[1])
	}
	if len(outputModules) > 8 {
		return nil, fmt.Errorf("too many output modules: %#v", split[1])
	}
	name := split[0]
	var moduleType communicationModuleType
	switch split[0][0] {
	case '%':
		moduleType = flipFlop
		name = name[1:]
	case '&':
		moduleType = conjunction
		name = name[1:]
	case 'b':
		moduleType = broadcast
	default:
		return nil, fmt.Errorf("invalid communication module type: %#v", split[0])
	}
	result := moduleIndex.get(name)
	result.moduleType = moduleType
	result.outputModules = make([]*parsedCommunicationModule, len(outputModules))
	for i, mod := range outputModules {
		outputModule := moduleIndex.get(mod)
		outputModule.senders |= result.mask
		outputModule.inputModules = append(outputModule.inputModules, result)
		receiver := moduleIndex.get(mod)
		result.outputModules[i] = receiver
	}

	return result, nil
}

type communicationModuleIndex map[string]*parsedCommunicationModule

func (idx communicationModuleIndex) get(name string) *parsedCommunicationModule {
	if module, ok := idx[name]; ok {
		return module
	}
	id := len(idx)
	if id >= 64 {
		panic("too many communication modules")
	}
	module := &parsedCommunicationModule{
		id:   id,
		mask: 1 << id,
		name: name,
	}
	idx[name] = module
	return module
}

type communicationModuleType uint8

const (
	untypedCommunicationModule communicationModuleType = iota
	flipFlop
	conjunction
	broadcast
)

type parsedCommunicationModule struct {
	mask       uint64
	senders    uint64
	moduleType communicationModuleType
	id         int

	name string

	inputModules  []*parsedCommunicationModule
	outputModules []*parsedCommunicationModule
}
