defmodule Problem0005Test do
  use ExUnit.Case, async: true
  use PropCheck
  doctest Problem0005

  describe "#{inspect(&Problem0005.solve/1)}:" do
    test "[base case 1] 1 step: matches correct answer" do
      assert Problem0005.solve(1) == 1
    end

    test "[base case 2] 2 steps: matches correct answer" do
      assert Problem0005.solve(2) == 2
    end

    property "[inductive case] step count >= 3: inductive solution", [
      :verbose
    ] do
      forall step_count <- integers_greater_than_n(3) do
        expected_result = Problem0005.solve(step_count - 1) + Problem0005.solve(step_count - 2)
        actual_result = Problem0005.solve(step_count)

        (Problem0005.solve(step_count) == expected_result)
        |> collect({:step_count, PropTestHelpers.bucket(step_count, 50)})
        |> when_fail(
          IO.puts("""
          Step count: #{step_count}
          Expected result: #{expected_result}
          Actual result: #{actual_result}
          """)
        )
      end
    end
  end

  ###
  ### Generators
  ###
  defp integers_greater_than_n(n) do
    sized(s, resize(s * 10, integer(n, :inf)))
  end
end
