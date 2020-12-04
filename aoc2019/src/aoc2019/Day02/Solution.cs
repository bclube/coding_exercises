using System.Collections.Immutable;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System;

namespace aoc2019.Day02
{
    public static class Solution
    {
        public static int SolveA()
        {
            var codes = ReadProgramInput();

            codes[1] = 12;
            codes[2] = 2;

            var result = ExecuteIntcodeProgram(new(codes));

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

                    var result = ExecuteIntcodeProgram(new(trial));

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

        public static IntcodeProgram ExecuteIntcodeProgram(IntcodeProgram program)
        {
            while (!Done(program))
            {
                program = ExecuteIntcodeProgramStep(program);
            }

            return program;
        }

        private static bool Done(IntcodeProgram program) =>
            program.Codes[program.CurrentInstruction] == 99;

        private static IntcodeProgram ExecuteIntcodeProgramStep(IntcodeProgram program)
        {
            var current = program.CurrentInstruction;
            var opCode = program.Codes[current++];
            if (opCode == 99)
                return program;

            Func<int, int, int> op = opCode switch
            {
                1 => (a, b) => a + b,
                2 => (a, b) => a * b,
                _ => throw new Exception($"Unknown op code {opCode}")
            };
            var a = program.Codes[program.Codes[current++]];
            var b = program.Codes[program.Codes[current++]];
            var resultIndex = program.Codes[current++];
            var result = op(a, b);

            var newCodes = program.Codes.SetItem(resultIndex, result);

            return new IntcodeProgram()
            {
                Codes = newCodes,
                CurrentInstruction = current
            };
        }
    }
}