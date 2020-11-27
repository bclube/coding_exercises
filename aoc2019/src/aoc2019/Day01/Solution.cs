using System;
using System.IO;
using System.Linq;

namespace aoc2019.Day01
{
    public static class Solution
    {
        public static int SolveA()
            => Solve(CalculateFuelRequirement);

        public static int SolveB()
            => Solve(CalculateFuelRequirementAdvanced);

        private static int Solve(Func<int, int> calculateFuelRequirement)
            => File.ReadLines("Day01/input.txt")
                .Select(ParseLine)
                .Select(calculateFuelRequirement)
                .Sum();

        private static int ParseLine(string line)
            => int.Parse(line);

        public static int CalculateFuelRequirement(int mass)
            => (mass / 3) - 2;

        public static int CalculateFuelRequirementAdvanced(int mass)
        {
            var totalFuelRequirement = 0;
            var remainingMass = mass;

            while (true)
            {
                remainingMass = CalculateFuelRequirement(remainingMass);

                if (remainingMass <= 0)
                    break;

                totalFuelRequirement += remainingMass;
            }

            return totalFuelRequirement;
        }
    }
}