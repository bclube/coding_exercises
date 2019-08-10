defmodule Problem0003 do
  @moduledoc """
  From dailycodingproblem.com:

  Given an array of integers, find the first missing positive integer in
  linear time and constant space. In other words, find the lowest positive
  integer that does not exist in the array. The array can contain duplicates
  and negative numbers as well.

  For example, the input [3, 4, -1, 1] should give 2. The input [1, 2, 0]
  should give 3.

  You can modify the input array in-place.
  """

  @doc """
  ## Examples

    iex> Problem0003.solve([])
    1

    iex> Problem0003.solve([0])
    1

    iex> Problem0003.solve([-1])
    1

    iex> Problem0003.solve([1])
    2

    iex> Problem0003.solve([3, 4, -1, 1])
    2

    iex> Problem0003.solve([1, 2, 0])
    3

  """
  def solve([]), do: 1

  def solve(ints) do
    # The instructions indicate that this should be solved in constant space
    # and that the array can be modified in-place. However, data structures in
    # Elixir are immutable, so this is not possible (or at least I'm not able
    # to think of a way to get arount this).
    #
    # I'll work around this limitation here and use a Map to simulate a mutable
    # array. This will allow a linear time solution using constant space (if
    # you don't count the creation of the Map and disregard the persistent
    # nature of the Elixir Map data structure).
    ints
    |> Stream.with_index(1)
    |> Map.new(fn {v, i} -> {i, v} end)
    |> sort_in_place()
    |> find_min_missing_value()
  end

  defp sort_in_place(values), do: sort_in_place(values, 1, map_size(values))

  defp sort_in_place(values, i, n) when i <= n do
    case Map.fetch!(values, i) do
      ^i ->
        sort_in_place(values, i + 1, n)

      v ->
        case swap_value(values, v, v) do
          {^v, new_map} -> sort_in_place(Map.replace!(new_map, i, nil), i + 1, n)
          {new_val, new_map} -> sort_in_place(Map.replace!(new_map, i, new_val), i, n)
        end
    end
  end

  defp sort_in_place(values, _i, _n), do: values

  defp find_min_missing_value(values) do
    values
    |> Stream.flat_map(fn
      {v, nil} -> [v]
      _other -> []
    end)
    |> Enum.min(fn -> map_size(values) + 1 end)
  end

  defp swap_value(values, key, value) do
    Map.get_and_update(values, key, fn
      nil -> :pop
      v -> {v, value}
    end)
  end
end
