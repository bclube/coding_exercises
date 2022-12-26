package main

import (
	"exercises/aoc2020/problem18"
	"fmt"
)

func main() {
	result, err := problem18.Solve()
	if err != nil {
		fmt.Println("Error:", err)
	} else {
		fmt.Println("Results:")
		fmt.Println("A:", result)
	}
}
