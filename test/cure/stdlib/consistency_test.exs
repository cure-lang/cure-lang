defmodule Cure.Stdlib.ConsistencyTest do
  @moduledoc """
  Guards the stdlib-consistency invariants the subagent audit flagged:

    * the `Option`/`Result` BEAM encoding is documented *once*, the same way,
      in every file that mentions it — and matches the compiler's actual
      erasure (`Cure.Elab.Emit.otp_tag/1`: `Ok` -> `:ok`, `Error` -> `:error`,
      `Some` -> `:some`, `None` -> `:none`);
    * the extractor naming convention is uniform across `core.cure`,
      `result.cure`, `option.cure`, and `match.cure`;
    * `@group` is always above its `mod` (spec
      2026-07-10-group-decorator-placement), and `@prelude` placement is
      either whole-module (above `mod`) or declaration-level (on a `type`),
      never a free-floating in-body statement.

  These are documentation/placement invariants, so they are checked against
  the source text rather than the elaborated AST.
  """
  use ExUnit.Case, async: true

  @std_dir Path.join([File.cwd!(), "lib", "std"])

  defp source(name), do: File.read!(Path.join(@std_dir, name))

  # ---------------------------------------------------------------------------
  # Option / Result BEAM encoding
  # ---------------------------------------------------------------------------

  describe "Option/Result BEAM encoding docs" do
    test "no stdlib file documents the capitalised (wrong) Some/None tags" do
      offenders =
        @std_dir
        |> Path.join("*.cure")
        |> Path.wildcard()
        |> Enum.filter(fn path ->
          src = File.read!(path)
          # The capitalised tags are never the real erasure; a doc that names
          # them is stale. `{:Some` / `{:None` / `{:Ok` / `{:Error` as
          # *encoding* claims are the audit's finding.
          src =~ ~r/\{:(?:Some|None|Ok|Error)\b/
        end)

      assert offenders == [],
             "these files document a capitalised BEAM tag that is never emitted: " <>
               Enum.map_join(offenders, ", ", &Path.basename/1)
    end

    test "core.cure documents the lowercase OTP encoding" do
      src = source("core.cure")
      assert src =~ "{:ok, v}"
      assert src =~ "{:error, e}"
      assert src =~ "{:some, v}"
      assert src =~ ":none"
    end

    test "option.cure documents the lowercase OTP encoding" do
      src = source("option.cure")
      assert src =~ "{:some, v}"
      assert src =~ ":none"
      refute src =~ "{:Some"
      refute src =~ ":None"
    end

    test "result.cure documents the lowercase OTP encoding" do
      src = source("result.cure")
      assert src =~ "{:ok, v}"
      assert src =~ "{:error, e}"
      refute src =~ "{:Ok"
      refute src =~ "{:Error"
    end
  end

  # ---------------------------------------------------------------------------
  # Extractor naming convention
  # ---------------------------------------------------------------------------

  describe "extractor naming convention" do
    test "Std.Option exposes unwrap and the unwrap_some synonym" do
      src = source("option.cure")
      assert src =~ "fn unwrap(opt: Option(t), default: t)"
      assert src =~ "fn unwrap_some(opt: Option(t), default: t)"
    end

    test "Std.Result exposes unwrap_ok, unwrap_error, and the unwrap synonym" do
      src = source("result.cure")
      assert src =~ "fn unwrap_ok(result: Result(t, e), default: t)"
      assert src =~ "fn unwrap_error(result: Result(t, e), default: e)"
      assert src =~ "fn unwrap(result: Result(t, e), default: t)"
    end

    test "Std.Match exposes all three Result/Option extractors" do
      src = source("match.cure")
      assert src =~ "fn unwrap_ok("
      assert src =~ "fn unwrap_error("
      assert src =~ "fn unwrap_some("
    end

    test "every file that documents the convention names the same four extractors" do
      for file <- ["option.cure", "result.cure", "match.cure"] do
        src = source(file)

        assert src =~ "Extractor naming",
               "#{file} is missing the extractor-naming note"
      end
    end
  end

  # ---------------------------------------------------------------------------
  # @group / @prelude placement
  # ---------------------------------------------------------------------------

  describe "decorator placement" do
    test "no stdlib file has @group inside the mod body" do
      offenders =
        @std_dir
        |> Path.join("*.cure")
        |> Path.wildcard()
        |> Enum.filter(&group_below_mod?/1)

      assert offenders == [],
             "these stdlib files still have @group inside the mod body: " <>
               Enum.map_join(offenders, ", ", &Path.basename/1)
    end

    test "@prelude is never a free-floating in-body statement" do
      # A declaration-level `@prelude` must sit directly above a `type` /
      # `typealias` / `fn`; a whole-module `@prelude` must sit above `mod`.
      # Anything else is a misplacement.
      offenders =
        @std_dir
        |> Path.join("*.cure")
        |> Path.wildcard()
        |> Enum.filter(&floating_prelude?/1)

      assert offenders == [],
             "these stdlib files have a mis-placed @prelude: " <>
               Enum.map_join(offenders, ", ", &Path.basename/1)
    end
  end

  # True iff the file's `@group(` line appears AFTER its `mod ` line.
  defp group_below_mod?(path) do
    lines = path |> File.read!() |> String.split("\n")
    group_idx = Enum.find_index(lines, &(&1 =~ ~r/^\s*@group\(/))
    mod_idx = Enum.find_index(lines, &(&1 =~ ~r/^\s*mod\s/))
    group_idx != nil and mod_idx != nil and group_idx > mod_idx
  end

  # True iff some `@prelude` line is not immediately followed (skipping blank
  # lines and `##` doc lines) by a `mod`, `type`, `typealias`, or `fn`.
  defp floating_prelude?(path) do
    lines = path |> File.read!() |> String.split("\n")

    lines
    |> Enum.with_index()
    |> Enum.any?(fn {line, idx} ->
      if line =~ ~r/^\s*@prelude\s*$/ do
        next = next_code_line(lines, idx + 1)
        next != nil and next =~ ~r/^\s*(mod|type|typealias|fn|opaque)\b/
      else
        false
      end
    end)
    |> Kernel.not()
  end

  # The next non-blank, non-doc, non-decorator line after `idx`, or nil.
  # Other decorators (`@builtin(...)`, a second `@prelude`) may stand between
  # `@prelude` and the declaration it annotates, so they are skipped too.
  defp next_code_line(lines, idx) do
    lines
    |> Enum.drop(idx)
    |> Enum.find(fn l ->
      trimmed = String.trim(l)

      trimmed != "" and not String.starts_with?(trimmed, "##") and
        not String.starts_with?(trimmed, "@")
    end)
  end
end
