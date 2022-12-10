package main

import (
	"exercises/aoc2020/problem12"
	"fmt"
)

func main() {
	resultA, resultB, err := problem12.Solve()
	if err != nil {
		fmt.Println("Error:", err)
	} else {
		fmt.Println("Results:")
		fmt.Println("A:", resultA)
		fmt.Println("B:", resultB)
	}
}
