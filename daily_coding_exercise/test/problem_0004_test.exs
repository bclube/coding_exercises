defmodule Problem0004Test do
  use ExUnit.Case, async: true
  use PropCheck
  doctest Problem0004

  setup_all do
    valid_codes = for n <- 1..26, do: Integer.to_string(n), into: MapSet.new()

    base_case_solutions =
      for(
        a <- valid_codes,
        String.length(a) == 1,
        b <- valid_codes,
        String.length(b) == 1,
        do: a <> b
      )
      |> Stream.concat(valid_codes)
      |> Enum.reduce(%{}, &Map.update(&2, &1, 1, fn v -> v + 1 end))

    [
      valid_codes: valid_codes,
      base_case_solution_lookup: &Map.get(base_case_solutions, &1, 0)
    ]
  end

  describe "#{inspect(&Problem0004.solve/1)}:" do
    test "[base case 1] all possible digit strings with length == 1: matches computed value", %{
      base_case_solution_lookup: base_case_solution_lookup
    } do
      for int <- 0..9, code = Integer.to_string(int) do
        expected_result = base_case_solution_lookup.(code)

        assert Problem0004.solve(code) == expected_result,
               """
               Failed with code: #{code}
               Expected result: #{expected_result}
               Actual result: #{Problem0004.solve(code)}
               """
      end
    end

    test "[base case 2] all possible digit strings with length == 2: matches computed value", %{
      base_case_solution_lookup: base_case_solution_lookup
    } do
      for a <- 0..9, b <- 0..9, code = Enum.join([a, b]) do
        expected_result = base_case_solution_lookup.(code)

        assert Problem0004.solve(code) == expected_result,
               """
               Failed with code: #{code}
               Expected result: #{expected_result}
               Actual result: #{Problem0004.solve(code)}
               """
      end
    end

    property "[inductive case] random code with length(code) >= 3: matches inductive proof",
             [
               :verbose
             ],
             %{
               valid_codes: valid_codes
             } do
      forall code <- code_with_three_or_more_characters() do
        {_, rest1} = String.split_at(code, 1)
        {prefix2, rest2} = String.split_at(code, 2)

        subresult1 = Problem0004.solve(rest1)

        subresult2 =
          if MapSet.member?(valid_codes, prefix2),
            do: Problem0004.solve(rest2),
            else: 0

        expected_result = subresult1 + subresult2

        (Problem0004.solve(code) == expected_result)
        |> collect({:code_length, PropTestHelpers.bucket(String.length(code), 10)})
        |> when_fail(
          IO.puts("""
          Code: #{code}
          Expected result: #{inspect(expected_result)}
          Actual result: #{inspect(Problem0004.solve(code))}
          """)
        )
      end
    end
  end

  ###
  ### Generators
  ###
  defp code_with_three_or_more_characters do
    let(
      {a, b, rest} <-
        such_that(
          {code1, code2, code_rest} <- {valid_code(), valid_code(), list(valid_code())},
          when: code1 > 9 || code2 > 9 || length(code_rest) > 0
        ),
      do: Enum.join([a, b | rest])
    )
  end

  defp valid_code do
    choose(1, 26)
  end
end
