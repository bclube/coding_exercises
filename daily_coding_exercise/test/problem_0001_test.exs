defmodule Problem0001Test do
  use ExUnit.Case, async: true
  use PropCheck
  doctest Problem0001

  describe "#{inspect(&Problem0001.contains_pair_with_sum?/2)}:" do
    property "random list => matches brute force result", [:verbose] do
      forall {ints, target_value} <- {list(int()), int()} do
        result = brute_force_result(ints, target_value)

        (result == Problem0001.contains_pair_with_sum?(ints, target_value))
        |> collect({
          if(result,
            do: :pair,
            else: :no_pair
          ),
          PropTestHelpers.bucket(length(ints), 5)
        })
      end
    end
  end

  ###
  ### Helpers
  ###
  defp brute_force_result([i | ints], target_value) do
    # Yes, this is O(n^2)
    Enum.any?(ints, &(&1 == target_value - i)) ||
      brute_force_result(ints, target_value)
  end

  defp brute_force_result([], _target_value), do: false
end
