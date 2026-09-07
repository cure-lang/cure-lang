defmodule Cure.Compiler.Parser.BuiltinMacros do
  @moduledoc """
  The built-in `:syntax`/`:computed` macro grammar and suffix-keyed `literal`
  rule set, harvested from every bundled stdlib (+ embedded Regex package)
  source and baked at Elixir COMPILE TIME.

  ## Why compile-time bake

  `Cure.Compiler.Parser.parse/2` seeds every parse with the stdlib's own macro
  grammar (`macro ... syntax ...` / `... computed ...` definitions declared in
  `lib/std/*.cure` and the embedded `lib/std_deps/regex/*.cure`), so a `use
  Std.Iter` file can use stdlib-provided syntax without the caller doing
  anything. Computing that grammar means parsing the WHOLE stdlib source tree
  three times over: a harvest pass with no active macros, a second reparse
  with that complete grammar seeded (so one stdlib macro can transparently
  invoke another), and a third pass for the suffix-keyed `literal` rules.

  Doing that lazily, memoized only in `:persistent_term`
  (`Cure.Compiler.Parser`'s previous implementation), is invisible within one
  long-lived process (a `cure repl` session, the Mix VM) but every FRESH
  `cure` escript invocation starts a brand new VM with an empty
  `persistent_term` table: `cure check`, the first line typed into a new
  `cure repl`, `cure run`, etc. paid the full multi-second harvest again on
  every single invocation, while any SUBSEQUENT operation in that same
  process reused the memo and looked instant — exactly the "first call is
  slow, every other call is fast" symptom this module exists to remove.

  Baking the result into a compile-time constant (mirroring
  `Cure.Compiler.Parser.BuiltinFixity`'s built-in operator table, for the
  identical reason) pays the harvest cost once, at build time, and makes
  `syntax_rules/0`/`literal_rules/0` free lookups thereafter — in a REPL
  session and in a fresh escript invocation alike.

  ## Compile order

  This module calls `Cure.Compiler.Parser.compute_prelude_macro_rules/1` at
  ITS OWN compile time, so `Parser` must already be compiled — exactly the
  same one-directional relationship `BuiltinFixity` has with `Parser.harvest/4`.
  `Parser` itself only reaches back into this module from ordinary function
  bodies (`prelude_macros/0`/`prelude_literal_macros/0`), a runtime call
  resolved long after both modules are compiled, so there is no compile
  cycle. Every harvested source parses with `prelude_macros: false`, so the
  bake never re-enters this module.

  Each harvested source is registered as an `@external_resource`, so editing
  a stdlib macro definition recompiles this module (and hence rebakes the
  grammar). A source file *added* to the stdlib that newly declares a macro
  is only picked up on a clean rebuild — the wildcard is evaluated once, at
  compile time.
  """

  alias Cure.Compiler.Parser

  # Captured at Elixir compile time, mirroring `BuiltinFixity`'s stdlib source
  # resolution (this module lives at the same `lib/cure/compiler/parser/`
  # depth, so the same three-levels-up relative path reaches `lib/`).
  @stdlib_source_dir Path.expand("../../../std", __DIR__)
  @regex_source_dir Path.expand("../../../std_deps/regex", __DIR__)

  @stdlib_macro_paths (Path.wildcard(Path.join(@stdlib_source_dir, "*.cure")) ++
                         Path.wildcard(Path.join(@regex_source_dir, "*.cure")))
                      |> Enum.sort()

  # Recompile (and rebake) when any stdlib source changes -- a macro
  # definition could appear or move in any of them.
  for path <- @stdlib_macro_paths do
    @external_resource path
  end

  # Bake the built-in macro grammar: harvest every bundled source (table- and
  # prelude-independent) and fold its declarations in. Runs at THIS module's
  # compile time; the result is frozen into the beam.
  {stdlib_macro_rules, stdlib_literal_macro_rules} =
    Parser.compute_prelude_macro_rules(@stdlib_macro_paths)

  @stdlib_macro_rules stdlib_macro_rules
  @stdlib_literal_macro_rules stdlib_literal_macro_rules

  @doc "The built-in `:syntax`/`:computed` macro rule set (a compile-time constant)."
  @spec syntax_rules() :: map()
  def syntax_rules, do: @stdlib_macro_rules

  @doc "The built-in suffix-keyed `literal` macro rule set (a compile-time constant)."
  @spec literal_rules() :: map()
  def literal_rules, do: @stdlib_literal_macro_rules
end
