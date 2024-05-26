package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
	"math/rand"
	"slices"
)

// This was solved with a randomized algorithm; it will find the correct solution with a high
// dregree of probability, but it is not guaranteed to find the correct solution. Running multiple
// times will increase the likelihood of finding the correct solution.
//
// The algorithm works by removing bridges from the graph until the graph is split into two
// disconnected components. We are told that there are exactly three connecting edges, so
// the code is specialized to that case.
//
// After removing the bridges, we count the number of reachable nodes and the number of unreachable
// nodes. The product of these two numbers is the solution.
func SolveDay25(ctx context.Context) (int, error) {
	for attempts := 0; attempts < 10; attempts++ {
		graph, err := parseComponentGraph(ctx, "day25.txt")
		if err != nil {
			return 0, err
		}
		err = removeBridges(ctx, graph)
		if err != nil {
			return 0, err
		}
		reachable := countReachable(ctx, graph)
		unreachable := len(graph) - reachable
		if reachable == 0 || unreachable == 0 {
			// most likely, we've removed an edge that was not actually a brigde.
			// Start over
			fmt.Println("retrying...")
			continue
		}
		fmt.Println("reachable", reachable, "unreachable", unreachable)
		return reachable * unreachable, nil
	}
	return 0, fmt.Errorf("no solution found")
}

func countReachable(ctx context.Context, graph componentConnections) int {
	visited := make([]bool, len(graph))
	return countReachableNodes(ctx, graph, 0, visited)
}

func countReachableNodes(ctx context.Context, graph componentConnections, from int, visited []bool) int {
	var count int
	for _, to := range graph[from] {
		if visited[to] {
			continue
		}
		visited[to] = true
		count++
		count += countReachableNodes(ctx, graph, to, visited)
	}
	return count
}

// This is a randomized solution and as such, it will not always find the correct solution.
// However, it does produce the correct solution a high percentage of the time.
//
// We are given that there are three bridges. If we choose two nodes that happen to be
// on different "islands", and we trace a number of random paths between them, the
// pigeonhole principle guarantees that there will be one node that is crossed by
// 1/3 of the paths, at minimum; we can conclude that this is a bridge. In a non-randomized
// solution, we would find that there is only one node that is crossed by 1/3 of the paths
// (according to my intuition, anyway: I have not proven this). Using a randomized approach
// gives a "good enough" solution with a high probability of success, but we lose the guarantee
// that we will find the correct solution.
//
// When we find a bridge, we remove it and repeat the process. This time, we will find a bridge
// that has at least 1/2 of the traffic, and we can remove that bridge. Finally, we will find
// a bridge that has all the traffic, and we can remove that bridge as well.
//
// If we get to the end and don't find an edge that has 100% of the traffic, we can conclude
// that we have removed an edge that was not actually a bridge. In that case, we start over.
func removeBridges(ctx context.Context, graph componentConnections) error {
	for round, trials := range []int{99, 30, 9} {
		remainingBridges := 3 - round
		bridge, err := findBridge(ctx, graph, remainingBridges, trials)
		if err == errNoBridgeDetected {
			fmt.Println("no bridge detected")
			continue
		}
		if err != nil {
			return err
		}
		fmt.Println("removing", bridge)
		for _, id := range []int{bridge.from, bridge.to} {
			g := graph[id]
			g = slices.DeleteFunc(g, func(i int) bool {
				return i == bridge.to || i == bridge.from
			})
			graph[id] = g
		}
	}
	return nil
}

func findBridge(ctx context.Context, graph componentConnections, remainingBridges, trials int) (pathKey, error) {
	const start = 0
	bridges := make(map[pathKey]int, len(graph))
	counts := make(map[pathKey]int, len(graph)*8)
	cutoff := trials / remainingBridges
nextStop:
	// Start by finding a path from the node with the highest id to the node with the lowest id.
	// This makes it more likely that the nodes we try early on will be on different "islands".
	// Again, I have not proven this, but it intuitively makes sense and in practice, it seems
	// to give the best results.
	for stop := len(graph) - 1; stop >= 1; stop-- {
		clear(counts)
		for trial := 0; trial < trials; trial++ {
			path, err := findRandomPath(ctx, graph, start, stop)
			if err != nil {
				return pathKey{}, err
			}
			for _, p := range path {
				if p.from > p.to {
					p.from, p.to = p.to, p.from
				}
				c := counts[p]
				c += 1
				if c >= cutoff {
					bridges[p]++
					// Only return a bridge if it has been detected at least twice.
					// This is to reduce the risk of false positives.
					if bridges[p] >= 2 {
						return p, nil
					} else {
						continue nextStop
					}
				}
				counts[p] = c
			}
		}
	}
	return pathKey{}, errNoBridgeDetected
}

var errNoBridgeDetected = fmt.Errorf("no bridge detected")

// findRandomPath is a function that finds a random path in a graph from a start node to a stop node.
func findRandomPath(ctx context.Context, graph componentConnections, start, stop int) ([]pathKey, error) {
	visited := make([]bool, len(graph))
	path := make([]pathKey, 0, len(graph))

tryAgain:
	for {
		next := start
		clear(visited)
		path = path[:0]
		visited[0] = true

		for next != stop {
			if ctx.Err() != nil {
				return nil, ctx.Err()
			}

			now := next
			gr := graph[now]

			i := rand.Intn(len(gr))
			for ii := 0; ii < len(gr); ii++ {
				next = gr[(i+ii)%len(gr)]
				if next == stop || !visited[next] {
					break
				}
			}
			if visited[next] {
				continue tryAgain
			}

			visited[next] = true
			path = append(path, pathKey{from: now, to: next})
		}

		return path, nil
	}
}

type pathKey struct {
	from int
	to   int
}

func parseComponentGraph(ctx context.Context, fileName string) (componentConnections, error) {
	lines, err := common.ReadAllLines(ctx, fileName)
	if err != nil {
		return componentConnections{}, err
	}
	ids := make(componentIds, len(lines)*3)

	graph := make(componentConnections, len(lines)*3)
	for _, line := range lines {
		cnn := make([]string, 0, 10)
		nm, err := parseComponentConnections(line, &cnn)
		if err != nil {
			return nil, err
		}
		from := ids.get(nm)
		for _, c := range cnn {
			to := ids.get(c)
			graph[from] = append(graph[from], to)
			graph[to] = append(graph[to], from)
		}
	}

	return graph[:len(ids)], nil
}

func parseComponentConnections(line string, connections *[]string) (string, error) {
	name := line[:3]
	for i := 5; i < len(line); i += 4 {
		*connections = append(*connections, line[i:i+3])
	}
	return name, nil
}

type componentConnections [][]int

type componentIds map[string]int

func (ids componentIds) get(name string) int {
	id, ok := ids[name]
	if !ok {
		id = len(ids)
		ids[name] = id
	}
	return id
}
