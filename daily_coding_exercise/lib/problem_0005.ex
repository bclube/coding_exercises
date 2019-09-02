defmodule Problem0005 do
  @moduledoc """
  From dailycodingproblem.com:

  There exists a staircase with N steps, and you can climb up either 1 or 2
  steps at a time. Given N, write a function that returns the number of
  unique ways you can climb the staircase. The order of the steps matters.

  For example, if N is 4, then there are 5 unique ways:

  1, 1, 1, 1
  2, 1, 1
  1, 2, 1
  1, 1, 2
  2, 2

  What if, instead of being able to climb 1 or 2 steps at a time, you could
  climb any number from a set of positive integers X? For example, if X = {1,
  3, 5}, you could climb 1, 3, or 5 steps at a time.
  """

  @doc """
  ## Examples

    iex> Problem0005.solve(1)
    1

    iex> Problem0005.solve(2)
    2

    iex> Problem0005.solve(4)
    5
  """
  def solve(1), do: 1
  def solve(2), do: 2
  def solve(n) when is_integer(n) and n >= 3, do: solve(n, 3, 3, 2)

  defp solve(n, n, a, _b), do: a
  defp solve(n, i, a, b), do: solve(n, i + 1, a + b, a)
end
