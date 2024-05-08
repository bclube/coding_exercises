package solution

import (
	"aoc2023/common"
	"context"
	"fmt"
)

/*
I solved day 24 by hand. Here's how:

  - We are (implicitly) given the fact that there exists only a single solution to the problem.

  - With the above point in mind, we know that we only need to look at three hailstones. Two of the hailstones
    may be coplanar, as long as the third is not coplanar with the other two. The proof is left to the reader.

  - We choose three hailstones based on the above points and label them A, B, and C.

  - Each hailstone path is written as a set of parametric equations:
    A: x = A.x + A.vel.x*a, y = A.y + A.vel.y*a, z = A.z + A.vel.z*a
    B: x = B.x + B.vel.x*b, y = B.y + B.vel.y*b, z = B.z + B.vel.z*b
    C: x = C.x + C.vel.x*c, y = C.y + C.vel.y*c, z = C.z + C.vel.z*c
    In the above equations, a, b, and c are the parameters that represent the time at which the hailstone is at a given position.
    It's important to note that the a, b, and c values are all in terms of the same overall time scale.
    I.e. at t = 1, a = 1, b = 1, and c = 1; at t = 100, a = 100, b = 100, and c = 100.

  - We find the equation of the slope of the line that passes through A and B:
    D = (B - A) / (b - a)
    x = ((B.x + B.vel.x*b) - (A.x + A.vel.x*a)) / (b - a)
    y = ((B.y + B.vel.y*b) - (A.y + A.vel.y*a)) / (b - a)
    z = ((B.z + B.vel.z*b) - (A.z + A.vel.z*a)) / (b - a)

  - Next we do the same for the line that passes through B and C:
    D = (C - B) / (c - b)
    x = ((C.x + C.vel.x*c) - (B.x + B.vel.x*b)) / (c - b)
    y = ((C.y + C.vel.y*c) - (B.y + B.vel.y*b)) / (c - b)
    z = ((C.z + C.vel.z*c) - (B.z + B.vel.z*b)) / (c - b)

  - Now we can find the times a, b, and c where the slopes between A and B, and B and C are equal. Note that depending
    on how A, B, and C are designated, we might not find a solution on the first try. This can happen if we get the order
    of the hailstones wrong. E.g. the slope of A to B might give us a vector in the reverse direction of the slope of B to C.
    If this happens, we need to swap the designations of the hailstones and try again. There may be more efficent ways to
    solve this problem, but this is what I did.

    To do this, we set the equations of the slopes equal to each other:
    ((B.x + B.vel.x*b) - (A.x + A.vel.x*a)) / (b - a) = ((C.x + C.vel.x*c) - (B.x + B.vel.x*b)) / (c - b)
    ((B.y + B.vel.y*b) - (A.y + A.vel.y*a)) / (b - a) = ((C.y + C.vel.y*c) - (B.y + B.vel.y*b)) / (c - b)
    ((B.z + B.vel.z*b) - (A.z + A.vel.z*a)) / (b - a) = ((C.z + C.vel.z*c) - (B.z + B.vel.z*b)) / (c - b)

    Then we solve the above system of equations for a, b; we can skip solving for c since we only need a and b:
    c = (B.x + B.vel.x*b - A.x - A.vel.x*a) / (B.vel.x - A.vel.x)
    c = (B.y + B.vel.y*b - A.y - A.vel.y*a) / (B.vel.y - A.vel.y)
    c = (B.z + B.vel.z*b - A.z - A.vel.z*a) / (B.vel.z - A.vel.z)

    Now, we set the c equations equal to each other:
    (B.x + B.vel.x*b - A.x - A.vel.x*a) / (B.vel.x - A.vel.x) = (B.z + B.vel.z*b - A.z - A.vel.z*a) / (B.vel.z - A.vel.z)
    (B.y + B.vel.y*b - A.y - A.vel.y*a) / (B.vel.y - A.vel.y) = (B.z + B.vel.z*b - A.z - A.vel.z*a) / (B.vel.z - A.vel.z)

    Then solve for b. Once you have two equations in the form b = ..., you can set them equal to each other and solve for b.
    Next, substitute the value of b into the equations for a to find a.
    We can stop at this point as you don't need the c value to find the final answer.

  - Once we have the times a and b where they are intersected by the transversal path of the rock, we can find the coordinates
    where hailstones A and B will be at these times.

  - We find the velocity of the transversal line by taking the difference of the two points and dividing by the difference in time:
    V = (B - A) / (b - a)
    x = ((B.x + B.vel.x*b) - (A.x + A.vel.x*a)) / (b - a)
    y = ((B.y + B.vel.y*b) - (A.y + A.vel.y*a)) / (b - a)
    z = ((B.z + B.vel.z*b) - (A.z + A.vel.z*a)) / (b - a)

  - Next we find the starting position of the rock by taking the position of A and subtracting the velocity of the line multiplied by the time a:
    x = A.x - A.vel.x*a
    y = A.y - A.vel.y*a
    z = A.z - A.vel.z*a

  - Finally, we add the x, y, and z coordinates of the rock to get the final answer.
*/
func SolveDay24(ctx context.Context) (int, error) {
	lines, err := common.ReadAllLines(ctx, "day24.txt")
	if err != nil {
		return 0, err
	}
	hailstones := make([]hailstoneMotion, len(lines))
	for i, line := range lines {
		h := &hailstones[i]
		n, err := fmt.Sscanf(line, "%d, %d, %d @ %d, %d, %d", &h.pos.x, &h.pos.y, &h.pos.z, &h.vel.x, &h.vel.y, &h.vel.z)
		if err != nil {
			return 0, err
		}
		if n != 6 {
			return 0, fmt.Errorf("expected 6 values, got %d", n)
		}
	}

	/*
		var coplanarHailstones []hailstoneMotion
		hs := make([]hailstoneMotion, 0, len(lines))
		for _, line := range lines {
			var h hailstoneMotion
			n, err := fmt.Sscanf(line, "%d, %d, %d @ %d, %d, %d", &h.pos.x, &h.pos.y, &h.pos.z, &h.vel.x, &h.vel.y, &h.vel.z)
			if err != nil {
				return 0, err
			}
			if n != 6 {
				return 0, fmt.Errorf("expected 6 values, got %d", n)
			}
			ii := slices.IndexFunc(hs, func(e hailstoneMotion) bool {
				return hailstonesAreCoplanar(h, e)
			})
			if ii >= 0 {
				if coplanarHailstones == nil {
					coplanarHailstones = []hailstoneMotion{h, hs[ii]}
					hs = slices.Delete(hs, ii, ii+1)
				}
				continue
			}
			hs = append(hs, h)
			if coplanarHailstones != nil && len(hs) >= 2 {
				break
			}
		}
		if coplanarHailstones == nil {
			return 0, fmt.Errorf("no coplanar hailstones found")
		}
		if len(hs) < 2 {
			return 0, fmt.Errorf("not enough hailstones to triangulate rock trajectory")
		}
		fmt.Println("coplanarHailstones:")
		fmt.Println("  ", coplanarHailstones[0])
		fmt.Println("  ", coplanarHailstones[1])
		fmt.Println("otherHailstones:")
		fmt.Println("  ", hs[0])
		fmt.Println("  ", hs[1])

		p1 := coplanarHailstones[0].pos
		p2 := coplanarHailstones[1].pos
		p3 := coplanarHailstones[1].pos
		p3.x += coplanarHailstones[1].vel.x
		p3.y += coplanarHailstones[1].vel.y
		p3.z += coplanarHailstones[1].vel.z

		var A hailstoneCoord
		A.x = p2.x - p1.x
		A.y = p2.y - p1.y
		A.z = p2.z - p1.z

		var B hailstoneCoord
		B.x = p3.x - p1.x
		B.y = p3.y - p1.y
		B.z = p3.z - p1.z

		var normal hailstoneCoord
		normal.x = A.y*B.z - A.z*B.y
		normal.y = A.z*B.x - A.x*B.z
		normal.z = A.x*B.y - A.y*B.x
		D := -normal.x*p1.x - normal.y*p1.y - normal.z*p1.z

		h := hs[0]
		// Find where and at what `t1` the `h` hailstone intersects the plane
		// normal.x*x + normal.y*y + normal.z*z + D = 0
		// normal.x*(h.pos.x + h.vel.x*t1) + normal.y*(h.pos.y + h.vel.y*t1) + normal.z*(h.pos.z + h.vel.z*t1) + D = 0
		// normal.x*h.pos.x + normal.y*h.pos.y + normal.z*h.pos.z + D + t1*(normal.x*h.vel.x + normal.y*h.vel.y + normal.z*h.vel.z) = 0
		// t1 = -(normal.x*h.pos.x + normal.y*h.pos.y + normal.z*h.pos.z + D) / (normal.x*h.vel.x + normal.y*h.vel.y + normal.z*h.vel.z)
		t1 := -(normal.x*h.pos.x + normal.y*h.pos.y + normal.z*h.pos.z + D) / (normal.x*h.vel.x + normal.y*h.vel.y + normal.z*h.vel.z)
		var h1Intersect hailstoneCoord
		h1Intersect.x = h.pos.x + h.vel.x*t1
		h1Intersect.y = h.pos.y + h.vel.y*t1
		h1Intersect.z = h.pos.z + h.vel.z*t1

		h = hs[1]
		t2 := -(normal.x*h.pos.x + normal.y*h.pos.y + normal.z*h.pos.z + D) / (normal.x*h.vel.x + normal.y*h.vel.y + normal.z*h.vel.z)
		var h2Intersect hailstoneCoord
		h2Intersect.x = h.pos.x + h.vel.x*t2
		h2Intersect.y = h.pos.y + h.vel.y*t2
		h2Intersect.z = h.pos.z + h.vel.z*t2

		if t2 > t1 {
			t1, t2 = t2, t1
			h1Intersect, h2Intersect = h2Intersect, h1Intersect
		}

		var solution hailstoneCoord
		solution.x = (h1Intersect.x*t2 - h2Intersect.x*t1) / (t2 - t1)
		solution.y = (h1Intersect.y*t2 - h2Intersect.y*t1) / (t2 - t1)
		solution.z = (h1Intersect.z*t2 - h2Intersect.z*t1) / (t2 - t1)

		fmt.Println("normal:", normal, D, t1, t2)
		fmt.Println("solution:", solution)

		return solution.x + solution.y + solution.z, nil
	*/

	return 0, nil
}

type hailstoneCoord struct {
	x, y, z int
}

type hailstoneMotion struct {
	pos hailstoneCoord
	vel hailstoneCoord
}
