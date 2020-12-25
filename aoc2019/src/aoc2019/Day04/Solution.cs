using System;
using System.Linq;
using System.Text.RegularExpressions;

namespace aoc2019.Day04
{
    public static class Solution
    {
        private const int MinPassword = 146810;
        private const int MaxPassword = 612564;

        public static int SolveA()
        {
            return Enumerable.Range(MinPassword, MaxPassword - MinPassword)
                .Select(p => p.ToString())
                .Where(IncreasingValue)
                .Where(ContainsRepeatedChar)
                .Count();
        }

        public static int SolveB()
        {
            return Enumerable.Range(MinPassword, MaxPassword - MinPassword)
                .Select(p => p.ToString())
                .Where(IncreasingValue)
                .Where(ContainsCharRepeatedExactlyTwice)
                .Count();
        }

        private static bool IncreasingValue(string str)
        {
            var prev = '!';

            foreach (var ch in str)
            {
                if (ch < prev)
                    return false;

                prev = ch;
            }

            return true;
        }

        private static bool ContainsRepeatedChar(string str)
            => str
                .GroupBy(c => c, (_, cs) => cs.Count())
                .Any(c => c > 1);

        private static bool ContainsCharRepeatedExactlyTwice(string str)
            => str
                .GroupBy(c => c, (_, cs) => cs.Count())
                .Any(c => c == 2);
    }
}