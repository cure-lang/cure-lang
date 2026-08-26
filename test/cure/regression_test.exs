defmodule Cure.RegressionTest do
  use ExUnit.Case, async: false
  # This deliberately recompiles and executes the complete example corpus. Its
  # duration scales with the corpus and with concurrent compiler-heavy tests, so
  # a wall-clock timeout would make `mix test` load-dependent.
  @moduletag timeout: :infinity

  @moduledoc """
  End-to-end regression coverage. These tests invoke the same logic as
  `mix cure.check` so a plain `mix test` run catches stdlib or example
  regressions too.
  """

  alias Mix.Tasks.Cure.Check

  # :slow — compiles all 126 stdlib modules through the strict public regression
  # task. The dependent stdlib now takes more than ExUnit's default 60-second
  # wall budget on a cold build, especially on the lower end of the CI matrix.
  # Keep a test-local ceiling: this remains a timeout, not an unbounded escape,
  # while ordinary tests retain the global 60-second deadlock guard.
  @tag :regression
  @tag :slow
  @tag timeout: 600_000
  test "every Std.* module compiles without warnings" do
    # `test_helper` makes canonical Std modules sticky to expose accidental
    # producer reloads. The strict regression task is a producer itself, so run
    # it in a clean VM just as CI's dedicated task invocation does.
    {result, status} =
      System.cmd("mix", ["cure.check.stdlib"],
        env: [{"MIX_ENV", "test"}],
        stderr_to_stdout: true
      )

    assert status == 0, result
    assert result =~ ~r/stdlib: \d+ passed, 0 failed/
  end

  @tag :regression
  test "every supported example compiles and produces the expected output" do
    preload_stdlib()

    result =
      ExUnit.CaptureIO.capture_io(fn ->
        try do
          Check.Examples.run([])
        catch
          :exit, {:shutdown, 1} -> flunk("examples regression failed")
        end
      end)

    refute result =~ "FAIL"
    assert result =~ ~r/examples: \d+ passed, \d+ skipped, 0 failed/
  end

  defp preload_stdlib do
    # Use the shared helper: loading beams by name instead of adding the
    # build dirs to the code path prevents stale lowercase leftovers from
    # shadowing OTP modules (notably `:math`) mid-suite. Explicit
    # `kind: :all` preserves the historical "load everything" behaviour
    # now that `Preload.preload/1` defaults to `:none`.
    Cure.Stdlib.Preload.preload(examples: true, kind: :all)
  end
end
