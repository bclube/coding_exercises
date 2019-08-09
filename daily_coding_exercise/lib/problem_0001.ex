defmodule Problem0001 do
  @moduledoc """
  From dailycodingproblem.com:

  Given a list of numbers and a number k, return whether any two numbers from the list add up to k.

  For example, given [10, 15, 3, 7] and k of 17, return true since 10 + 7 is 17.

  Bonus: Can you do this in one pass?
  """

  @doc """
  Returns whether any two numbers in the given list add up to the given target sum.

  ## Examples

      iex> Problem0001.contains_pair_with_sum?([10, 15, 3, 7], 17)
      true

  """
  def contains_pair_with_sum?(ints, target_sum) do
    contains_pair_with_sum_impl(ints, target_sum, MapSet.new())
  end

  defp contains_pair_with_sum_impl([], _target_sum, _matches), do: false

  defp contains_pair_with_sum_impl([i | ints], target_sum, matches) do
    MapSet.member?(matches, i) ||
      contains_pair_with_sum_impl(ints, target_sum, MapSet.put(matches, target_sum - i))
  end
end
