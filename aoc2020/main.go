package main

import (
	"exercises/aoc2020/problem01"
	"fmt"
)

func main() {
	resultA, resultB, err := problem01.Solve()
	if err != nil {
		println(err)
	} else {
		fmt.Println("Results:")
		fmt.Println("A:", resultA)
		fmt.Println("B:", resultB)
	}
}
