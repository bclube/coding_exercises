using System.Collections;
using System.Collections.Generic;
using NUnit.Framework;
using FluentAssertions;
using aoc2019.Day02;

namespace aoc2019.Tests
{
    [TestFixture]
    public class Day02Tests
    {
        private static IEnumerable IntcodeProgramTestCases()
        {
            yield return new[]{
                new IntcodeProgram(1,0,0,0,99),
                new IntcodeProgram(2,0,0,0,99){ CurrentInstruction = 4 }
            };
            yield return new[]{
                new IntcodeProgram(2,3,0,3,99),
                new IntcodeProgram(2,3,0,6,99){ CurrentInstruction = 4 }
            };
            yield return new[]{
                new IntcodeProgram(2,4,4,5,99,0),
                new IntcodeProgram(2,4,4,5,99,9801){ CurrentInstruction = 4 }
            };
            yield return new[]{
                new IntcodeProgram(1,1,1,4,99,5,6,0,99),
                new IntcodeProgram(30,1,1,4,2,5,6,0,99){ CurrentInstruction = 8 }
            };
        }

        [TestCaseSource(nameof(IntcodeProgramTestCases))]
        public void ExecuteIntcodeProgram_HappyPath_ReturnsExpectedResult(IntcodeProgram program, IntcodeProgram expectedResult)
        {
            var result = aoc2019.Day02.Solution.ExecuteIntcodeProgram(program);

            result.Codes.Should().BeEquivalentTo(expectedResult.Codes);
            result.CurrentInstruction.Should().Be(expectedResult.CurrentInstruction);
        }
    }
}