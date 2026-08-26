defmodule Cure.Stdlib.DependentEmitParityTest do
  @moduledoc """
  #18-readiness firewall, EMIT tier. The companion
  `dependent_elaboration_parity_test.exs` proves every `@green` stdlib module
  *elaborates* on the dependent pipeline. This one proves the strictly stronger
  property that actually gates the classic rip-out: each module completes the
  full DEPENDENT CODEGEN path and produces real BEAM function forms.

  Today the committed stdlib modules are syntactically non-dependent, so
  `Cure.Compiler.codegen/5` routes them through the CLASSIC codegen
  (`Cure.Elab.Program.dependent?/1` is false). Deleting the classic pipeline
  (#18) makes `codegen` route EVERY module through `Cure.Elab.Emit`
  unconditionally. So the question that decides whether the rip-out is a clean
  delete is not "does it elaborate" but "does the dependent emitter lower it to
  loadable forms." This test runs exactly the private `dependent_codegen/1`
  sequence (`check_ast_with_locals` → `Emit.compile_forms`) against each module
  and locks the answer in as an immutable regression: a future change that breaks
  dependent emission of a stdlib module is caught HERE, before rip-out, rather
  than discovered mid-teardown.

  The `@green` list mirrors the elaboration firewall's and only ever grows. The
  same seven modules are held out for the same reasons (show/io/access/set are
  classic-coexistence-blocked; http/regex are AtomVM dead-ends; pair is slated
  for retirement) — see `dependent_elaboration_parity_test.exs`. They emit
  through the dependent pipeline only after their rip-out rewrites land.
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

  # Rich modules that must emit a substantial function surface — guards against a
  # silent regression where emission "succeeds" but degrades to empty/hollow forms.
  @min_forms %{"list" => 20, "map" => 10, "string" => 15, "math" => 12, "result" => 8}

  defp dependent_codegen(name) do
    src = File.read!(Path.join("lib/std", name <> ".cure"))

    with {:ok, tokens} <- Lexer.tokenize(src, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         {:ok, env, locals} <- Program.check_ast_with_locals(ast),
         {:ok, forms} <- Emit.compile_forms(env, Program.module_atom(ast), locals) do
      {:ok, forms}
    end
  end

  test "every dependent-green stdlib module lowers to BEAM forms via the dependent emitter" do
    failures =
      Enum.reduce(@green, [], fn name, acc ->
        result =
          try do
            dependent_codegen(name)
          rescue
            e -> {:raise, Exception.message(e)}
          catch
            kind, value -> {:raise, "#{inspect(kind)}: #{inspect(value)}"}
          end

        case result do
          {:ok, forms} when is_list(forms) -> acc
          other -> [{name, inspect(other, limit: 5)} | acc]
        end
      end)

    assert failures == [],
           "stdlib modules failed dependent emission (rip-out would break on these):\n" <>
             Enum.map_join(Enum.reverse(failures), "\n", fn {n, e} -> "  Std.#{n}: #{e}" end)
  end

  test "rich stdlib modules emit their full function surface (no hollow-emit regression)" do
    shortfalls =
      Enum.reduce(@min_forms, [], fn {name, floor}, acc ->
        {:ok, forms} = dependent_codegen(name)
        fun_count = Enum.count(forms, &match?({:function, _, _, _, _}, &1))
        if fun_count >= floor, do: acc, else: [{name, fun_count, floor} | acc]
      end)

    assert shortfalls == [],
           "stdlib modules emitted fewer function forms than expected:\n" <>
             Enum.map_join(shortfalls, "\n", fn {n, got, floor} ->
               "  Std.#{n}: emitted #{got} functions, expected >= #{floor}"
             end)
  end

  # The classic-coexistence contract, EMIT tier. `show`/`io` cannot appear in
  # `@green` because their committed files omit `use Std.String` + `use
  # Std.Semigroup` (the classic checker breaks on List(Char) strings). Their
  # elaboration side is guarded in dependent_elaboration_parity_test.exs; this
  # locks the stronger property that once those held-out imports are supplied
  # (as `Cure.Stdlib.Preload` would at rip-out) the dependent emitter lowers them
  # to real BEAM forms — so they are emit-ready, not merely type-correct, when
  # classic is deleted.
  @coexistence [{"show", ~w(Std.String Std.Semigroup)}, {"io", ~w(Std.String Std.Semigroup)}]

  test "classic-coexistence modules (show/io) emit once their held-out imports are added" do
    failures =
      Enum.reduce(@coexistence, [], fn {name, uses}, acc ->
        src = inject_uses(Path.join("lib/std", name <> ".cure"), uses)

        result =
          try do
            with {:ok, tokens} <- Lexer.tokenize(src, emit_events: false),
                 {:ok, ast} <- Parser.parse(tokens, emit_events: false),
                 {:ok, env, locals} <- Program.check_ast_with_locals(ast),
                 {:ok, forms} <- Emit.compile_forms(env, Program.module_atom(ast), locals) do
              {:ok, Enum.count(forms, &match?({:function, _, _, _, _}, &1))}
            end
          rescue
            e -> {:raise, Exception.message(e)}
          catch
            kind, value -> {:raise, "#{inspect(kind)}: #{inspect(value)}"}
          end

        case result do
          {:ok, n} when n > 0 -> acc
          other -> [{name, inspect(other, limit: 5)} | acc]
        end
      end)

    assert failures == [],
           "classic-coexistence modules no longer emit with imports (emit green-on-" <>
             "deletion contract broken):\n" <>
             Enum.map_join(Enum.reverse(failures), "\n", fn {n, e} -> "  Std.#{n}: #{e}" end)
  end

  # Insert `use <mod>` lines immediately after the `mod …` header, mirroring the
  # elaboration firewall's helper and how Preload supplies them at rip-out.
  defp inject_uses(path, uses) do
    lines = String.split(File.read!(path), "\n")
    {pre, [mod_line | post]} = Enum.split_while(lines, &(not String.match?(&1, ~r/^\s*mod\s/)))
    use_lines = Enum.map(uses, &("  use " <> &1))
    Enum.join(pre ++ [mod_line] ++ use_lines ++ post, "\n")
  end
end
