using System.Collections.Immutable;
using System.Collections.Generic;

namespace aoc2019.Day02
{
    public record IntcodeProgram
    {
        public int CurrentInstruction { get; init; } = 0;
    public ImmutableList<int> Codes { get; init; } = ImmutableList<int>.Empty;
    public IntcodeProgram(IEnumerable<int> codes)
    {
        Codes = ImmutableList<int>.Empty.AddRange(codes);
    }

    public IntcodeProgram(params int[] codes)
    {
        Codes = ImmutableList<int>.Empty.AddRange(codes);
    }
}
}