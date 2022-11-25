package main

import (
	"exercises/aoc2020/problem04"
	"fmt"
)

func main() {
	resultA, resultB, err := problem04.Solve()
	if err != nil {
		fmt.Println("Error:", err)
	} else {
		fmt.Println("Results:")
		fmt.Println("A:", resultA)
		fmt.Println("B:", resultB)
	}
}
