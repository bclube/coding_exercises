package solution

import (
	"context"
	"sort"
)

func SolveDay06(ctx context.Context) (int, error) {
	duration := 59707878
	currentRecord := 430121812131276

	// find smallest value that beats the record
	smallest := sort.Search(duration, func(i int) bool {
		return i*(duration-i) > currentRecord
	})

	// find the value that is one higher than the highest value that beats the record
	largest := sort.Search(duration, func(i int) bool {
		return duration > smallest &&
			i*(duration-i) < currentRecord
	})

	ways := largest - smallest

	return ways, nil
}
