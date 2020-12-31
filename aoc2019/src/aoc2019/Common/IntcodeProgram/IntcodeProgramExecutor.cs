using System.Collections.Immutable;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System;
using aoc2019.Common.IntcodeProgram;

namespace aoc2019.Common.IntcodeProgram
{
    public static class IntcodeProgramExecutor
    {
        public static IntcodeProgramState ExecuteIntcodeProgram(IntcodeProgramState program)
        {
            while (!Done(program))
            {
                program = ExecuteIntcodeProgramStep(program);
            }

            return program;
        }

        private static bool Done(IntcodeProgramState program) =>
            program.Codes[program.CurrentInstruction] == 99;

        private static IntcodeProgramState ExecuteIntcodeProgramStep(IntcodeProgramState program)
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

            return new IntcodeProgramState()
            {
                Codes = newCodes,
                CurrentInstruction = current
            };
        }
    }
}
