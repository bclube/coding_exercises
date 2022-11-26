package main

import (
	"exercises/aoc2020/problem08"
	"fmt"
)

func main() {
	resultA, resultB, err := problem08.Solve()
	if err != nil {
		fmt.Println("Error:", err)
	} else {
		fmt.Println("Results:")
		fmt.Println("A:", resultA)
		fmt.Println("B:", resultB)
	}
}
