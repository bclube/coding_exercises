package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
)

const (
	gardenRock       = '#'
	gardenPlot       = '.'
	startingPosition = 'S'
	oddGardenPlot    = '_'
)

/*
This solution is optimized for the provided data set for day 21; it is not a general solution.

Observation of the data set:
- The garden is a square grid: 131x131
- The starting position is the exact center of the garden: (65, 65)
- There are garden plots leading directly from the starting position to the edge of the garden in all four directions
- There are garden plots surrounding the entire map
- The reachable area within 65 steps forms a diamond shape
Based on these observations, it follows that:
- You can get from the center of any map to the center of any adjacent map in 131 steps
- You can look at the grid of garden maps as a 2D array of garden plots, where each unit of 131 steps moves you to the next map in the grid
- The target number of steps is 26501365, which is (202,300 * 131) + 65. I.e. 202,300 maps in any direction to the center of a map, and 65 steps from there to the edge of the traversable area
- In the same way, you can travel 202,299 maps in one direction and then turn 90 degrees and travel 1 map in another direction, and from there you can go 65 spaces.
- Altogether, the traversable area forms a perfect diamond shape all all garden plots reachable in 26501365 steps
More observations:
- Since each grid is a square with an odd number of spaces, adjacent map grids are inverses of one another. In other words, if you can reach a space
in an odd number of steps on one map, you can reach the same space in an adjacent map in an even number of steps.
e o e o e . o e o e o
o e o e o . e o e o e
e o e o e . o e o e o
o e o e o . e o e o e
e o e o e . o e o e o

We want to count all plots that are reachable in an odd number of steps.
One way to find the answer is to look at each square in a single map grid and determine how many times it is visited in all. For example:
in the overall grid of 404601*404601 maps, in how many of these maps is the square at (0, 0) visited? Then answer the same question for (0, 1) and so on.
The answer is the sum of these amounts.

It turns out that the squares in the upper left, upper right, lower left, and lower right corners of the map are visited in exactly one half of the maps (rounded down).
These squares are designated by the diagram below (this is a smaller version of the 131x131 map, but illustrates the point):
xxxxx.xxxxx
xxxx...xxxx
xxx.....xxx
xx.......xx
x.........x
...........
x.........x
xx.......xx
xxx.....xxx
xxxx...xxxx
xxxxx.xxxxx

I will not go into the full proof here. It happens that the squares in the outer triangles are visted in consecutive even numbered runs of maps on the map.
Since each adjacent map is the inverse of the adjacent maps, the number of times each square in the outer triangles is reachable in an odd number
of steps in exactly 1/4 of the total number of maps (rounded down).

Similarly, we can determine how many times each square in the inner diamond is visited:
.....x.....
....xxx....
...xxxxx...
..xxxxxxx..
.xxxxxxxxx.
xxxxxxxxxxx
.xxxxxxxxx.
..xxxxxxx..
...xxxxx...
....xxx....
.....x.....

This is a little more complicated, as they occur in consecutive runs of ODD numbers of maps. It turns out that there are two types of squares in the inner diamond:
I will leave out the proof, but these factors are derived from the squares of the inner diamond:
For example, for a 5x5 map, the outer triangle factor is 6 (i.e. (5 * 5) / 4 [rounded down]) the inner diamond factors are 9 and 4 (i.e. 3 * 3 and 2 * 2).
Notice that 3 + 2 = 5. Notice also that 25 = (6 * 2) + 9 + 4
For a 201x201 map, the outer factor is 10100 (i.e. (201 * 201) / 4 [rounded down]); the inner factors are 10000 and 10,201 (i.e. 100 * 100 and 101 * 101).
Notice that 100 + 101 = 201. Notice also that 40,401 = (10,100 * 2) + 10,000 + 10,201

The major and minor factors are distributed as follows, where `M` is a major factor and `m` is a minor factor:
...M...
..MmM..
.MmMmM.
MmMmMmM
.MmMmM.
..MmM..
...M...

In other words, the number of times the squares are visited overall, is equal to the major or minor factor of that square.

Keep in mind that not all squares on the garden map are reachable; some squares contain rocks and some are surrounded by rocks, making them unreachable. Such squares do not contribute to the overall count.
*/
func SolveDay21(ctx context.Context) (int, error) {
	// This solution calcualates the correct answer, but it needs TLC. It does not follow good programming practices.
	// I'm leaving it as-is for now, so I can move on to other problems.
	grid, err := common.ReadByteGrid(ctx, "day21.txt")
	if err != nil {
		return 0, err
	}
	const goal = 26501365
	mapHeight := len(grid)
	stepsToEdge := mapHeight / 2
	fmt.Println("steps to the edge of the initial map", stepsToEdge)
	mapSquaresToEdge := (goal - stepsToEdge) / mapHeight
	fmt.Println("map widths traversed in total after that", mapSquaresToEdge)
	greaterMapWidth := mapSquaresToEdge*2 + 1
	fmt.Println("so in total, the entire world is", greaterMapWidth, "maps wide")
	totalNumberOfMaps := greaterMapWidth * greaterMapWidth
	fmt.Println("and there are", totalNumberOfMaps, "maps in total (i.e. length * width)")
	outerFactor := totalNumberOfMaps / 4
	fmt.Println("outer factor", outerFactor, "(i.e. totalNumberOfMaps / 4 [truncated])")
	half := greaterMapWidth / 2
	innerMinorFactor := half * half
	fmt.Println("inner minor factor", innerMinorFactor, "(i.e. half * half)")
	half += 1
	innerMajorFactor := half * half
	fmt.Println("inner major factor", innerMajorFactor, "(i.e. half * half)")
	check := 2*outerFactor + innerMinorFactor + innerMajorFactor
	fmt.Println("check", check)
	var r, c int
	for i, row := range grid {
		for j, cell := range row {
			if cell == startingPosition {
				r, c = i, j
				break
			}
		}
	}
	var (
		outer,
		innerMajor,
		innerMinor int
	)
	fmt.Println(r, c)
	q := make([]gardenMapTraverser, 0, len(grid)*len(grid[0]))
	for _, traverser := range []gardenMapTraverser{
		{0, 0, 64, &outer, &outer},
		{0, 130, 64, &outer, &outer},
		{130, 0, 64, &outer, &outer},
		{130, 130, 64, &outer, &outer},
		{r, c, 66, &innerMinor, &innerMajor},
	} {
		queue := append(q, traverser)
		for len(queue) > 0 {
			var traverser gardenMapTraverser
			traverser, queue = queue[0], queue[1:]
			//fmt.Println(traverser)
			switch {
			case traverser.row < 0 || traverser.row >= len(grid):
				continue
			case traverser.col < 0 || traverser.col >= len(grid[0]):
				continue
			case grid[traverser.row][traverser.col] != gardenPlot &&
				grid[traverser.row][traverser.col] != startingPosition:
				continue
			case traverser.remainingSteps%2 == 0:
				*traverser.evenPlots++
				grid[traverser.row][traverser.col] = oddGardenPlot
			default:
				*traverser.oddPlots++
				grid[traverser.row][traverser.col] = oddGardenPlot
			}
			if traverser.remainingSteps == 0 {
				continue
			}
			remainingSteps := traverser.remainingSteps - 1
			queue = append(queue,
				gardenMapTraverser{traverser.row, traverser.col - 1, remainingSteps, traverser.evenPlots, traverser.oddPlots},
				gardenMapTraverser{traverser.row, traverser.col + 1, remainingSteps, traverser.evenPlots, traverser.oddPlots},
				gardenMapTraverser{traverser.row - 1, traverser.col, remainingSteps, traverser.evenPlots, traverser.oddPlots},
				gardenMapTraverser{traverser.row + 1, traverser.col, remainingSteps, traverser.evenPlots, traverser.oddPlots},
			)
		}
	}
	for _, row := range grid {
		fmt.Println(string(row))
	}

	total := outer*outerFactor +
		innerMajor*innerMajorFactor +
		innerMinor*innerMinorFactor
	fmt.Println("inner major", innerMajor, "inner minor", innerMinor, "outer", outer)
	return total, nil
}

type gardenMapTraverser struct {
	row, col, remainingSteps int
	evenPlots, oddPlots      *int
}
