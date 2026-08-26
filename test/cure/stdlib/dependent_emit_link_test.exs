defmodule Cure.Stdlib.DependentEmitLinkTest do
  @moduledoc """
  #18-readiness firewall, LINK tier — strictly stronger than the EMIT tier and
  the one the classic rip-out actually stands on. `dependent_emit_parity_test`
  proves each stdlib module's forms are PRODUCED by the dependent emitter; it
  runs `Emit.compile_forms` per module IN ISOLATION and never compiles the forms.
  That missed a whole class of defect: forms can be well-shaped yet reference an
  undefined function. A `use`-imported cross-module call (`code_point` from
  `Std.Char`, `Std.List.map`, `compare_string` from `Std.Comparable`) was lowered
  as a LOCAL Erlang call `code_point/1`, which BEAM lint rejects as undefined —
  so six `@green` modules (comparable, core, test, functor, non_empty, gen) would
  have broken the moment the classic pipeline was deleted and every module routed
  through `Cure.Elab.Emit`.

  This tier runs the emitted forms through `:compile.forms` (the BEAM linter):
  every local call must resolve to a local function or a BIF, and every export be
  well-formed. Cross-module calls are now emitted as REMOTE calls
  (`'Cure.Std.Char':code_point/1`), which lint accepts, via
  canonical owner identities threaded directly into `Emit.compile_forms/3`. A
  module whose forms fail to lint is caught HERE, before rip-out, not mid-teardown.

  The `@green` list mirrors the emit/elaboration firewalls and only grows. The
  same seven modules are held out for the same reasons (show/io/access/set are
  classic-coexistence-blocked; http/regex are AtomVM dead-ends; pair is slated
  for retirement).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  # actor/app/fsm/process/supervisor were removed with the container compilers
  # (#18); concurrency is now pure `@extern` wrappers, not their own modules.
  @green ~w(
    atom binary bool bounded char comparable core crdt decision equatable
    equivalent float functor gen int iter json list map match math nat
    non_empty option proof result semigroup sigma string
    system telescope test time tuple unit vector
  )

  # Emit `lib/std/<name>.cure` through the dependent pipeline using canonical
  # owner identities, then run the forms through the BEAM linter. Returns `:ok` when the module
  # lints clean, `{:lint_error, errors}` when a call/export does not resolve.
  defp emit_and_lint(name) do
    src = File.read!(Path.join("lib/std", name <> ".cure"))
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env, locals} = Program.check_ast_with_locals(ast)
    {:ok, forms} = Emit.compile_forms(env, Program.module_atom(ast), locals)

    case :compile.forms(forms, [:return_errors, :return_warnings, :nowarn_unused_vars]) do
      {:ok, _mod, _bin} -> :ok
      {:ok, _mod, _bin, _warnings} -> :ok
      {:error, errors, _warnings} -> {:lint_error, errors}
    end
  end

  test "every dependent-green stdlib module's emitted forms pass BEAM lint (link-clean)" do
    failures =
      Enum.reduce(@green, [], fn name, acc ->
        case emit_and_lint(name) do
          :ok -> acc
          {:lint_error, errors} -> [{name, inspect(errors, limit: 8)} | acc]
        end
      end)

    assert failures == [],
           "stdlib modules emitted forms that fail BEAM lint (rip-out would break " <>
             "on these — undefined cross-module calls):\n" <>
             Enum.map_join(Enum.reverse(failures), "\n", fn {n, e} -> "  Std.#{n}: #{e}" end)
  end
end
