package solution

import (
	"aoc2023/common"
	"context"

	"golang.org/x/sync/errgroup"
)

func SolveDay04(ctx context.Context) (int, error) {
	g, ctx := errgroup.WithContext(ctx)
	lines, lineReader := common.LinesFromFile(ctx, "day04.txt")
	g.Go(lineReader)

	cardCounts := [223]int{}

	var sum int
	i := -1
	g.Go(common.ForEach(ctx, lines, func(ctx context.Context, line string) error {
		i++
		cardCounts[i]++

		winningNumbers := [10]string{}
		ns := line[10:40]
		for i := 0; i < 10; i++ {
			ii := i * 3
			winningNumbers[i] = ns[ii : ii+2]
		}
		var matches int
		ns = line[42:]
		for i := 0; i < 25; i++ {
			ii := i * 3
			num := ns[ii : ii+2]
			for _, winningNumber := range winningNumbers {
				if num == winningNumber {
					matches++
				}
			}
		}
		for j := 1; j <= matches; j++ {
			cardCounts[i+j] += cardCounts[i]
		}
		sum += cardCounts[i]
		return nil
	}))

	return sum, g.Wait()
}
