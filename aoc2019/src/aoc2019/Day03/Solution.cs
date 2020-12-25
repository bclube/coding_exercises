using System.Text.RegularExpressions;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System;

namespace aoc2019.Day03
{
    public static class Solution
    {
        public static int SolveA()
        {
            var input = ReadProgramInput();
            var paths = GeneratePaths(input);
            var intersections = FindIntersections(paths);
            return LeastManhattanDistance(intersections);
        }

        public static int SolveB()
        {
            var input = ReadProgramInput();
            var paths = GeneratePaths(input);
            return paths
                .Select(ps => ps
                    .Select((p, i) => (p, i: i + 1))
                    .Deduplicate(p => p.p))
                .Aggregate((a, b) =>
                    a.Join(b,
                        a => a.p,
                        b => b.p,
                        (a, b) => (a.p, a.i + b.i)))
                .Select(f => f.i)
                .Min();
        }

        private static IEnumerable<T> Deduplicate<T, TKey>(this IEnumerable<T> vs, Func<T, TKey> keySelector)
        {
            var seen = new HashSet<TKey>();

            return vs.Where(v => seen.Add(keySelector(v)));
        }

        private static int LeastManhattanDistance(IEnumerable<(int, int)> intersections)
            => intersections
                .Select(a => Math.Abs(a.Item1) + Math.Abs(a.Item2))
                .Min();

        private static IEnumerable<(int, int)> FindIntersections(IEnumerable<IEnumerable<(int, int)>> paths)
            => paths.Aggregate((a, b) => a.Intersect(b));

        private static IEnumerable<IEnumerable<(int, int)>> GeneratePaths(IEnumerable<IEnumerable<Segment>> input)
            => input.Select(GeneratePath);

        private static IEnumerable<(int, int)> GeneratePath(IEnumerable<Segment> line)
        {
            var x = 0;
            var y = 0;

            foreach (var segment in line)
            {
                var (dx, dy) = segment.Direction switch
                {
                    Direction.Up => (1, 0),
                    Direction.Down => (-1, 0),
                    Direction.Right => (0, 1),
                    Direction.Left => (0, -1),
                    _ => (0, 0)
                };

                for (int i = 0; i < segment.Magnitude; i++)
                {
                    x = x + dx;
                    y = y + dy;
                    yield return (x, y);
                }
            }
        }

        private static IEnumerable<IEnumerable<Segment>> ReadProgramInput()
            => File
                .ReadLines("Day03/input.txt")
                .Select(ParseLine);

        private static IEnumerable<Segment> ParseLine(string line)
            => line
                .Split(',', StringSplitOptions.TrimEntries)
                .Select(ParseSegment);

        private static readonly Regex segmentRegex = new Regex(@"([UDLR])(\d+)");

        private static Segment ParseSegment(string segment)
        {
            var parsed = segmentRegex.Match(segment);
            var dir = parsed.Groups[1].Value switch {
                "U" => Direction.Up,
                "D" => Direction.Down,
                "L" => Direction.Left,
                "R" => Direction.Right,
                _ => throw new Exception("Parse error")
            };
            var magnitude = int.Parse(parsed.Groups[2].Value);

            return new Segment
            {
                Direction = dir,
                Magnitude = magnitude
            };
        }
    }

    public enum Direction
    {
        Up,
        Down,
        Left,
        Right
    }

    public record Segment
    {
        public Direction Direction { get; init; }
        public int Magnitude { get; init; }
    }
}