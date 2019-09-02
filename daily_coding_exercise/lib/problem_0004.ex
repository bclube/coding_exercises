defmodule Problem0004 do
  @moduledoc """
  From dailycodingproblem.com:

  Given the mapping a = 1, b = 2, ... z = 26, and an encoded message, count
  the number of ways it can be decoded.

  For example, the message '111' would give 3, since it could be decoded as
  'aaa', 'ka', and 'ak'.

  You can assume that the messages are decodable. For example, '001' is not
  allowed.
  """

  @doc """
  ## Examples

    iex> Problem0004.solve("")
    0

    iex> Problem0004.solve("1")
    1

    iex> Problem0004.solve("26")
    2

    iex> Problem0004.solve("111")
    3

  """
  def solve(""), do: 0

  def solve(encoded) when is_binary(encoded) do
    encoded
    |> String.graphemes()
    |> Stream.map(&String.to_integer/1)
    |> Enum.reverse()
    |> solve_impl()
  end

  defp solve_impl([d | rest]) do
    solve_impl(rest, d, lookup_single(d), 1)
  end

  defp solve_impl([d | rest], d2, p1, p2) do
    subresult =
      lookup_double(d, d2) * p2 +
        lookup_single(d) * p1

    solve_impl(rest, d, subresult, p1)
  end

  defp solve_impl([], _d, p1, _p2), do: p1

  defp lookup_single(d) when d > 0, do: 1
  defp lookup_single(_), do: 0

  defp lookup_double(1, _), do: 1
  defp lookup_double(2, b) when b <= 6, do: 1
  defp lookup_double(_, _), do: 0
end
