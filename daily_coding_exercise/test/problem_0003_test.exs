defmodule Problem0003Test do
  use ExUnit.Case, async: true
  use PropCheck
  doctest Problem0003

  describe "#{inspect(&Problem0003.solve/1)}:" do
    property "random list: solution > 0" do
      forall ints <- list(int()) do
        Problem0003.solve(ints) > 0
      end
    end

    property "random list: solution <= length(list) + 1" do
      forall ints <- list(int()) do
        Problem0003.solve(ints) <= length(ints) + 1
      end
    end

    property "random list: matches brute force result", [:verbose] do
      forall ints <- list(int()) do
        sorted =
          ints
          |> Stream.filter(&(&1 > 0))
          |> Stream.uniq()
          |> Enum.sort()

        expected_result =
          sorted
          |> Stream.with_index(1)
          |> Enum.find(fn {v, i} -> v != i end)
          |> case do
            {_v, i} -> i
            nil -> length(sorted) + 1
          end

        result = Problem0003.solve(ints)

        (expected_result == result)
        |> when_fail(
          IO.puts("""
          Expected result: #{inspect(expected_result)}
          Actual result: #{inspect(result)}
          """)
        )
      end
    end
  end
end
