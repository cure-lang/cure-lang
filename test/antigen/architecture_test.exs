defmodule Antigen.ArchitectureTest do
  use ExUnit.Case, async: true

  test "no Generators.* or Assays.* source references StreamData" do
    offenders =
      Path.wildcard("lib/antigen/{generators,assays}/**/*.ex")
      |> Enum.filter(fn f -> File.read!(f) =~ ~r/\bStreamData\b/ end)

    assert offenders == [], "StreamData leaked into: #{inspect(offenders)}"
  end
end
