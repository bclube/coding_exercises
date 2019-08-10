defmodule Problem0002 do
  @moduledoc """
  From dailycodingproblem.com:

  Given an array of integers, return a new array such that each element at
  index i of the new array is the product of all the numbers in the original
  array except the one at i.

  For example, if our input was [1, 2, 3, 4, 5], the expected output would be
  [120, 60, 40, 30, 24]. If our input was [3, 2, 1], the expected output
  would be [2, 3, 6].

  Follow-up: what if you can't use division?
  """

  @doc """
  ## Examples

    iex> Problem0002.solve([])
    []

    iex> Problem0002.solve([5])
    [1]

    iex> Problem0002.solve([5, 7])
    [7, 5]

    iex> Problem0002.solve([3, 2, 1])
    [2, 3, 6]

    iex> Problem0002.solve([1, 2, 3, 4, 5])
    [120, 60, 40, 30, 24]

  """
  def solve([]), do: []

  def solve(ints) do
    products_from_tail =
      ints
      |> Stream.drop(1)
      |> Enum.reverse()
      |> Enum.scan(&Kernel.*/2)
      |> Enum.reverse()
      |> Stream.concat([1])

    Stream.concat([1], Stream.scan(ints, &Kernel.*/2))
    |> Stream.zip(products_from_tail)
    |> Enum.map(fn {a, b} -> a * b end)
  end
end
