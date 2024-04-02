package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
)

func lcm(numbers ...int) int {
	if len(numbers) == 0 {
		return 0
	}
	result := numbers[0]
	for _, n := range numbers[1:] {
		result *= n / gcd(result, n)
	}
	return result
}

func gcd(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func SolveDay08(ctx context.Context) (int, error) {
	desertMap, err := parseDesertNetwork(ctx)
	if err != nil {
		return 0, err
	}
	// NOTE: This is not a general solution; it is optimized for the provided data set.
	// Of note, this solution will NOT work for the test data set.
	// The provided data set contains six traversers; each with a different cycle length
	leastCommonMultiple := findCycle(ctx, desertMap.startingNodes[0], desertMap.directions)
	for _, t := range desertMap.startingNodes[1:] {
		cycle := findCycle(ctx, t, desertMap.directions)
		leastCommonMultiple = lcm(leastCommonMultiple, cycle)
	}
	return leastCommonMultiple, nil
}

func findCycle(ctx context.Context, fromNode *desertNetworkNode, directions string) int {
	var currentInstruction int
	firstNode, distanceToFirstEndNode := findNextEndNode(fromNode, &currentInstruction, directions)
	if currentInstruction != 0 {
		// observation of provided data shows that each traverser ends up at the same end node
		// in the same number of steps, every time. The current instruction always ends up as zero.
		// Panic if this invariant is violated.
		panic("unexpected currentInstruction")
	}
	nextNode, cycleDistance := findNextEndNode(firstNode, &currentInstruction, directions)
	if currentInstruction != 0 {
		// observation of provided data shows that each traverser ends up at the same end node
		// in the same number of steps, every time. The current instruction always ends up as zero.
		// Panic if this invariant is violated.
		panic("unexpected currentInstruction")
	}
	if firstNode != nextNode {
		// observation of provided data shows that each traverser ends up at the same end node
		// in the same number of steps, every time. The current instruction always ends up as zero.
		// Panic if this invariant is violated.
		panic("cycle mismatch")
	}
	if distanceToFirstEndNode != cycleDistance {
		fmt.Println(distanceToFirstEndNode, cycleDistance)
		// observation of provided data shows that each traverser ends up at the same end node
		// in the same number of steps, every time. The current instruction always ends up as zero.
		// Panic if this invariant is violated.
		panic("cycle distance mismatch")
	}
	return cycleDistance
}

func findNextEndNode(startNode *desertNetworkNode, currentInstruction *int, directions string) (
	endNode *desertNetworkNode,
	distance int,
) {
	endNode = startNode
	for {
		distance++
		switch directions[*currentInstruction] {
		case 'L':
			endNode = endNode.left
		case 'R':
			endNode = endNode.right
		}
		*currentInstruction = (*currentInstruction + 1) % len(directions)
		if endNode.endNode {
			return
		}
	}
}

func parseDesertNetwork(ctx context.Context) (*desertMap, error) {
	lines, err := common.ReadAllLines(ctx, "day08.txt")
	if err != nil {
		return nil, err
	}

	nodeIndex := make(map[string]struct {
		left  string
		right string
		node  *desertNetworkNode
	}, len(lines))
	startingNodes := make([]*desertNetworkNode, 0, len(lines))

	directions := lines[0]
	for _, line := range lines[2:] {
		node := &desertNetworkNode{}
		switch line[2] {
		case 'A':
			startingNodes = append(startingNodes, node)
		case 'Z':
			node.endNode = true
		}
		nodeName := line[:3]
		nodeIndex[nodeName] = struct {
			left  string
			right string
			node  *desertNetworkNode
		}{
			left:  line[7:10],
			right: line[12:15],
			node:  node,
		}
	}

	for _, node := range nodeIndex {
		node.node.left = nodeIndex[node.left].node
		node.node.right = nodeIndex[node.right].node
	}

	return &desertMap{
		directions:    directions,
		startingNodes: startingNodes,
	}, nil
}

type desertMap struct {
	directions    string
	startingNodes []*desertNetworkNode
}

type desertNetworkNode struct {
	left    *desertNetworkNode
	right   *desertNetworkNode
	endNode bool
}
