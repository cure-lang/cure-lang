defmodule Cure.Core.NoBoolPrimitiveTest do
  use ExUnit.Case, async: true

  @core_files Path.wildcard("lib/cure/core/*.ex")

  test "no core module references the retired primitive Bool forms" do
    offenders =
      for f <- @core_files,
          src = File.read!(f),
          tok <- ~w(:bool_elim :bool_type :bool_lit :vbool :vbool_type :nbool_elim),
          String.contains?(src, tok),
          do: {Path.basename(f), tok}

    assert offenders == [], "still present: #{inspect(offenders)}"
  end
end
