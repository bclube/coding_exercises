defmodule Circuit.MixProject do
  use Mix.Project

  def project do
    [
      app: :circuit,
      version: "0.1.0",
      elixir: "~> 1.9",
      elixirc_paths: elixirc_paths(Mix.env()),
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  defp elixirc_paths(:test), do: ["lib", "test/"]
  defp elixirc_paths(_), do: ["lib"]

  def application do
    [
      extra_applications: [:logger]
    ]
  end

  defp deps do
    [
      {:circuit_breaker,
       git: "https://github.com/klarna/circuit_breaker.git", tag: "1.0.1", manager: :rebar3},
      {:propcheck, "~> 1.1", only: [:test, :dev]},
      {:simplehttp, "~> 0.5.1"}
    ]
  end
end
