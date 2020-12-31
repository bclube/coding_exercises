using System.Collections.Immutable;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System;
using aoc2019.Common.IntcodeProgram;

namespace aoc2019.Day02
{
    public static class Solution
    {
        public static int SolveA()
        {
            var codes = ReadProgramInput();

            codes[1] = 12;
            codes[2] = 2;

            var result = IntcodeProgramExecutor.ExecuteIntcodeProgram(new(codes));

            return result.Codes[0];
        }

        public static int SolveB()
        {
            var codes = ReadProgramInput().ToImmutableList();

            for (int noun = 0; noun <= 99; noun++)
            {
                for (int verb = 0; verb <= 99; verb++)
                {
                    var trial = codes
                        .SetItem(1, noun)
                        .SetItem(2, verb);

                    var result = IntcodeProgramExecutor.ExecuteIntcodeProgram(new(trial));

                    if (result.Codes[0] == 19690720)
                        return 100 * noun + verb;
                }
            }

            throw new Exception("Not able to find solution");
        }

        private static int[] ReadProgramInput()
        {
            return File.ReadLines("Day02/input.txt")
                .First()
                .Split(',', StringSplitOptions.TrimEntries)
                .Select(int.Parse)
                .ToArray();
        }
    }
}