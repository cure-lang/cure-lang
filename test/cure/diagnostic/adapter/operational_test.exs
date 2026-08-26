defmodule Cure.Diagnostic.Adapter.OperationalTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Adapter.Operational
  alias Cure.Diagnostic.Renderer

  test "the operational family converter owns host failures without changing their public output" do
    error = {:file_read_error, "missing.cure", :enoent}
    diagnostic = Operational.from_error(error)
    compatibility = Cure.Diagnostic.Operational.from_error(error)

    assert compatibility == diagnostic
    assert diagnostic.code == "E095"
    assert diagnostic.payload == %{path: "missing.cure", reason: ":enoent"}

    assert Renderer.plain(diagnostic, nil, width: 80) ==
             """
             -- COULD NOT READ FILE [E095] --------------------------------------------------

             Cannot read `missing.cure`: no such file or directory
             """
             |> String.trim_trailing()
  end

  test "the operational family has no generic ordinary-error fallback" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      Operational.from_error({:ordinary_source_failure, :must_use_a_family_converter})
    end
  end
end
