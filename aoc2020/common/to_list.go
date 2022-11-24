package common

func ToSlice[T any](in <-chan T, capacity int) []T {
	result := make([]T, 0, capacity)
	for v := range in {
		result = append(result, v)
	}
	return result
}
