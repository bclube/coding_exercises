package main

import (
	"exercises/aoc2020/problem02"
	"fmt"
)

func main() {
	resultA, resultB, err := problem02.Solve()
	if err != nil {
		println(err)
	} else {
		fmt.Println("Results:")
		fmt.Println("A:", resultA)
		fmt.Println("B:", resultB)
	}
}
