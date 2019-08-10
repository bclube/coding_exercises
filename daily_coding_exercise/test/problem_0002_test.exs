defmodule Problem0002Test do
  use ExUnit.Case, async: true
  use PropCheck
  doctest Problem0002

  describe "#{inspect(&Problem0002.solve/1)}:" do
    property "random list => length of output == length of input" do
      forall ints <- list(int()) do
        ints
        |> Problem0002.solve()
        |> length()
        |> Kernel.==(length(ints))
      end
    end

    property "random list => matches brute force result", [:verbose] do
      forall ints <- list(int()) do
        expected_result = brute_force_result(ints)
        result = Problem0002.solve(ints)

        (result == expected_result)
        |> collect({:list_length, ints |> length() |> PropTestHelpers.bucket(5)})
        |> collect({:number_of_zeroes, Enum.count(ints, &(&1 == 0))})
        |> when_fail(
          IO.puts("""
          input: #{inspect(ints)}
          brute force result: #{inspect(expected_result)}
          actual result: #{inspect(result)}
          """)
        )
      end
    end
  end

  defp brute_force_result([]), do: []

  defp brute_force_result(ints) do
    # Yes, this is O(n^2)
    for i <- 0..(length(ints) - 1) do
      ints
      |> Stream.with_index()
      |> Stream.reject(&match?({_v, ^i}, &1))
      |> Stream.map(&elem(&1, 0))
      |> Enum.reduce(1, &Kernel.*/2)
    end
  end
end
