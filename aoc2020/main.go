package main

import (
	"exercises/aoc2020/problem14"
	"fmt"
)

func main() {
	resultA, resultB, err := problem14.Solve()
	if err != nil {
		fmt.Println("Error:", err)
	} else {
		fmt.Println("Results:")
		fmt.Println("A:", resultA)
		fmt.Println("B:", resultB)
	}
}
