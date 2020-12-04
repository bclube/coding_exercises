using NUnit.Framework;
using FluentAssertions;

namespace aoc2019.Tests
{
    public class Day01Tests
    {
        [TestCase(12, 2)]
        [TestCase(14, 2)]
        [TestCase(1969, 654)]
        [TestCase(100756, 33583)]
        public void CalculateFuelRequirement_HappyPath_ReturnsExpectedResult(int mass, int expectedResult)
        {
            var result = aoc2019.Day01.Solution.CalculateFuelRequirement(mass);

            result.Should().Be(expectedResult);
        }

        [TestCase(14, 2)]
        [TestCase(1969, 966)]
        [TestCase(100756, 50346)]
        public void CalculateAdditionalFuelRequirement_HappyPath_ReturnsExpectedResult(int mass, int expectedResult)
        {
            var result = aoc2019.Day01.Solution.CalculateFuelRequirementAdvanced(mass);

            result.Should().Be(expectedResult);
        }
    }
}