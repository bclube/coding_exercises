package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
	"maps"
	"sync/atomic"

	"golang.org/x/sync/errgroup"
)

// This solution works, but it needs a lot of refactoring
func SolveDay23(ctx context.Context) (int, error) {
	grid, err := common.ReadByteGrid(ctx, "day23.txt")
	if err != nil {
		return 0, err
	}
	graph := make(forestGraph, 0)
	grid[0][1] = forestPathNode
	err = getForestGraph(ctx, forestPathTraverser{1, 1}, grid, graph)
	if err != nil {
		return 0, err
	}
	fmt.Println("graph nodes:", len(graph))
	backtrack := make(map[forestPathTraverser]struct{}, len(graph))
	length, err := maxForestPath(ctx, graph, forestPathTraverser{0, 1}, backtrack)
	if err != nil {
		return 0, err
	}
	return length, nil
}

const (
	forestPathNode          byte = 'o'
	traversedForestPathNode byte = 'x'
	forestPathBondary       byte = '#'
)

func maxForestPath(ctx context.Context, graph forestGraph, traverser forestPathTraverser, backtrack map[forestPathTraverser]struct{}) (int, error) {
	edges := graph[traverser]
	if len(edges) == 1 && traverser.r != 0 {
		// found exit
		return 0, ctx.Err()
	}
	var count int
	for _, edge := range edges {
		if _, contains := backtrack[edge.to]; !contains {
			count++
		}
	}
	if count == 0 {
		return 0, ctx.Err()
	}
	var g *errgroup.Group
	backtrack[traverser] = struct{}{}
	defer delete(backtrack, traverser)
	// only go concurrent when it can make a difference; i.e. early on in the graph traversal
	// and when there are multiple paths to explore
	if len(backtrack) <= 16 && count >= 2 {
		g, ctx = errgroup.WithContext(ctx)
	}
	var max int32
	for i, edge := range edges {
		if _, contains := backtrack[edge.to]; contains {
			continue
		}
		if g != nil {
			edge := edge
			backtrack := backtrack
			if i < len(edges)-1 {
				backtrack = maps.Clone(backtrack)
			}
			g.Go(func() error {
				length, err := maxForestPath(ctx, graph, edge.to, backtrack)
				if err != nil {
					return err
				}
				length += edge.length
				for {
					oldMax := atomic.LoadInt32(&max)
					if length <= int(oldMax) {
						break
					}
					if atomic.CompareAndSwapInt32(&max, oldMax, int32(length)) {
						break
					}
				}
				return nil
			})
		} else {
			length, err := maxForestPath(ctx, graph, edge.to, backtrack)
			if err != nil {
				return 0, err
			}
			length += edge.length
			if length > int(max) {
				max = int32(length)
			}
		}
	}
	if g == nil {
		return int(max), ctx.Err()
	}
	return int(max), g.Wait()
}

func getForestGraph(ctx context.Context, traverser forestPathTraverser, grid [][]byte, graph forestGraph) error {
	var from forestPathTraverser
	length := 1
	exits := make([]forestPathTraverser, 0, 3)
	for {
		exits = exits[:0]
		for _, next := range [4]forestPathTraverser{
			{traverser.r - 1, traverser.c},
			{traverser.r, traverser.c + 1},
			{traverser.r + 1, traverser.c},
			{traverser.r, traverser.c - 1},
		} {
			switch {
			case next.r < 0 || next.r >= len(grid) || next.c < 1 || next.c >= len(grid[0]):
				continue
			case grid[next.r][next.c] == forestPathBondary || grid[next.r][next.c] == traversedForestPathNode:
				continue
			case grid[next.r][next.c] == forestPathNode:
				// assume all paths have length > 1; that way we can avoid backtracking
				if length == 1 {
					from = next
					continue
				}
				graph.addNode(from, next, length+1)
				return ctx.Err()
			case next.r == len(grid)-1:
				// forest path exit
				grid[traverser.r][traverser.c] = traversedForestPathNode
				grid[next.r][next.c] = forestPathNode
				graph.addNode(from, next, length+1)
				return ctx.Err()
			default:
				exits = append(exits, next)
			}
		}
		grid[traverser.r][traverser.c] = traversedForestPathNode
		if len(exits) == 0 {
			return ctx.Err()
		}
		if len(exits) != 1 {
			break
		}
		traverser = exits[0]
		length++
	}

	grid[traverser.r][traverser.c] = forestPathNode
	graph.addNode(from, traverser, length)

	for _, exit := range exits {
		err := getForestGraph(ctx, exit, grid, graph)
		if err != nil {
			return err
		}
	}

	return ctx.Err()
}

type forestPathTraverser struct {
	r, c int
}

type forestGraphEdge struct {
	to     forestPathTraverser
	length int
}

type forestGraph map[forestPathTraverser][]forestGraphEdge

func (g forestGraph) addNode(from, to forestPathTraverser, length int) {
	g[from] = append(g[from], forestGraphEdge{to, length})
	g[to] = append(g[to], forestGraphEdge{from, length})
}
