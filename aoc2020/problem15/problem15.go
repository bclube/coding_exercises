package problem15

func Solve() (int, int, error) {
	ints := []int{1, 0, 18, 10, 19, 6}
	return SolveBoth(ints)
}

func SolveBoth(ints []int) (int, int, error) {
	latest := map[int]int{}
	for i, v := range ints[:len(ints)-2] {
		latest[v] = i
	}
	lastA := ints[len(ints)-2]
	next := ints[len(ints)-1]
	i := len(ints) - 1
	for ; i < 2020; i++ {
		latest[lastA] = i - 1
		lastA = next
		if v, exists := latest[next]; exists {
			next = i - v
		} else {
			next = 0
		}
	}
	lastB := lastA
	for ; i < 30000000; i++ {
		latest[lastB] = i - 1
		lastB = next
		if v, exists := latest[next]; exists {
			next = i - v
		} else {
			next = 0
		}
	}
	return lastA, lastB, nil
}
