defmodule Cure.Compiler.Parser.BuiltinFixity do
  @moduledoc """
  The built-in operator `FixityTable`, harvested from the compiler-bundled
  `@prelude` stdlib operator sources (today only `operators.cure`).

  This lives in the compiler/parser layer — not in `Cure.Stdlib.Preload` — so
  the Pratt parser can reach it at *bootstrap*. `Preload` bakes its stdlib
  dependency maps at Elixir compile time by running `DepGraph.scan/1`, which
  re-enters `Parser.parse/2`; the parser needs the built-in fixity table to bind
  operators (and the `.` projection) correctly while that scan runs, but
  `Preload`'s own module is not yet available during its compilation. Housing the
  table here — a module compiled before `Preload` — breaks that cycle: the parser
  depends only on this module, never on `Preload`.

  ## Compile-time bake

  The table is a compile-time constant. When *this* module compiles, it harvests
  every bundled `@prelude` stdlib source that declares a fixity and folds the
  declarations into a `FixityTable` (`@builtin_fixity_table`). `table/0` then
  just returns that constant — no runtime filesystem access, no `persistent_term`
  memo, no recomputation. This is what makes it robust in packaged / escript
  builds: a distributed `cure` calls `table/0` every time it parses a `.cure`
  file, and a constant baked into the beam works identically wherever it runs,
  whereas a runtime `Path.wildcard` over the compile-time source directory would
  depend on that directory still existing at the original path.

  The harvest runs at *this* module's compile time, so it compile-depends on
  `Parser`/`Lexer`/`FixityScan`/`Edition`/`FixityTable`. None of those
  compile-depend back on this module (`Parser` calls `table/0` only from function
  bodies — a runtime edge), so there is no compile cycle. `Parser.harvest/4` is
  table-independent (it seeds an explicit `base` and never consults
  `session_builtin_fixity_table/0`), so the bake cannot re-enter `table/0`.

  Each harvested source is registered as an `@external_resource`, so editing an
  operator source recompiles this module (and hence rebakes the table). A source
  file *added* to the stdlib that newly declares a fixity is only picked up on a
  clean rebuild — the wildcard is evaluated once, at compile time.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Compiler.Parser.{FixityTable, FixityScan}

  # Captured at Elixir compile time from the in-tree `lib/std/`.
  @stdlib_source_dir Path.expand("../../../std", __DIR__)

  # Cheap textual gate: a source with no fixity-declaration keyword contributes
  # nothing to the fixity table, so it is skipped before the expensive harvest.
  # Semantically identical to harvesting every file (a skipped file folds to
  # nothing) and keeps the model uniform: no module is named; ANY `@prelude` file
  # that declares a fixity is picked up. Today only `operators.cure` matches.
  @fixity_kw ~r/^\s*(infix|prefix|postfix|precedencegroup)\b/m
  @prelude_kw ~r/^\s*@prelude\b/m

  # The bundled stdlib sources that syntactically declare a fixity, resolved once
  # at compile time via the fixed `@stdlib_source_dir` wildcard — independent of
  # the project source universe, so the baked table can't vary with it.
  @prelude_fixity_sources @stdlib_source_dir
                          |> Path.join("*.cure")
                          |> Path.wildcard()
                          |> Enum.sort()
                          |> Enum.filter(fn path ->
                            case File.read(path) do
                              {:ok, source} ->
                                Regex.match?(@prelude_kw, source) and Regex.match?(@fixity_kw, source)

                              _ ->
                                false
                            end
                          end)

  # Recompile (and rebake) when an operator source changes.
  for path <- @prelude_fixity_sources do
    @external_resource path
  end

  # Bake the built-in table: harvest each `@prelude` fixity source (table-
  # independent) and fold its declarations in. Runs at THIS module's compile
  # time; the result is frozen into the beam.
  @builtin_fixity_table Enum.reduce(@prelude_fixity_sources, FixityTable.new(), fn path, acc ->
                          with {:ok, source} <- File.read(path),
                               {:ok, tokens} <- Lexer.tokenize(source, emit_events: false) do
                            logical_path = Path.join(["lib", "std", Path.basename(path)])
                            exprs = Parser.harvest(tokens, logical_path, FixityTable.new(), Cure.Edition.current())

                            if FixityScan.prelude?(exprs),
                              do: FixityScan.build_table(exprs, acc),
                              else: acc
                          else
                            _ -> acc
                          end
                        end)

  @doc "The built-in fixity table (a compile-time constant)."
  @spec table() :: FixityTable.t()
  def table, do: @builtin_fixity_table

  @doc """
  Extend an existing `FixityTable` with the `precedencegroup`/`infix`/… decls
  found in `ast`. Used by the parser to layer a module's own fixity declarations
  onto the built-in table.
  """
  @spec extend(FixityTable.t(), term()) :: FixityTable.t()
  def extend(base, ast), do: FixityScan.build_table(ast, base)
end
