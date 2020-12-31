using System.Collections.Immutable;
using System.Collections.Generic;

namespace aoc2019.Common.IntcodeProgram
{
    public record IntcodeProgramState
    {
        public int CurrentInstruction { get; init; } = 0;
        public ImmutableList<int> Codes { get; init; } = ImmutableList<int>.Empty;
        public IntcodeProgramState(IEnumerable<int> codes)
        {
            Codes = ImmutableList<int>.Empty.AddRange(codes);
        }

        public IntcodeProgramState(params int[] codes)
        {
            Codes = ImmutableList<int>.Empty.AddRange(codes);
        }
    }
}
