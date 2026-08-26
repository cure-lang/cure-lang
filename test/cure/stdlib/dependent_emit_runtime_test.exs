defmodule Cure.Stdlib.DependentEmitRuntimeTest do
  @moduledoc """
  #18-readiness firewall, RUNTIME tier — the strongest of the three. The
  elaboration firewall proves stdlib modules type-check on the dependent
  pipeline; the emit firewall proves they lower to BEAM forms. Neither proves the
  emitted code actually WORKS: well-typed, well-formed forms can still be
  runtime-wrong (a mis-erased constructor tag, a wrong arity, an off-by-one in a
  recursive lowering). This tier emits each module through the dependent pipeline,
  LOADS the BEAM, and RUNS its functions, asserting concrete results.

  It locks in the actual post-rip-out runtime behavior, including the canonical
  constructor representation: the OTP-conventional `Option`/`Result` constructors
  erase to lowercase BEAM tags (`some(42) == {:some, 42}`, `none() == :none`,
  `ok(7) == {:ok, 7}`, `error(:bad) == {:error, :bad}`) so a Cure value is a
  native OTP term that Erlang/Elixir and AtomVM FFI consume directly. Non-OTP
  constructors keep their declared (PascalCase) tag; records stay tagged tuples.

  The chosen modules are self-contained (no cross-module runtime dependency that
  would need separate loading): `option`/`result` exercise the ADT tag
  representation, `math` a pure-value `@extern` surface, `list` recursion + list
  externs, `bool` boolean logic. Together they show the dependent emitter yields
  correct runnable code across the shapes the stdlib is built from.

  This is an emitter-verifying PRODUCER: it deliberately re-emits stdlib modules
  through the dependent pipeline to prove the emitter's output *runs*. Under the
  C1 sticky-canonical regime (`test/test_helper.exs`) it must NOT emit under the
  bare canonical name — that slot is loaded and sticky at suite startup, so a
  canonical-name load fails with `:sticky_directory`. So it emits each module
  under a per-test module-name PREFIX (`T_<module>.Cure.Std.X`, C2), keeping the
  exact `Emit.compile_and_load` path under test while never touching the shared
  canonical slot. `async: false` is retained as defence-in-depth against two runs
  racing to define the same prefixed atom, not for correctness.
  """
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  # Emit `lib/std/<name>.cure` through the dependent pipeline under a per-test
  # PREFIX and load the BEAM, returning the loaded (prefixed) module atom. Passing
  # the module's own owner as `local_owners` keeps any same-owner remote call
  # pointed at the prefixed module rather than the sticky canonical; these modules
  # are self-contained, so there is no cross-owner delegation to reroute.
  defp load_std(name) do
    src = File.read!(Path.join("lib/std", name <> ".cure"))
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, env, locals} = Program.check_ast_with_locals(ast)

    canonical = Program.module_atom(ast)
    owner = canonical |> Atom.to_string() |> String.replace_prefix("Cure.", "")
    prefix = prefix_for(__MODULE__)

    {:ok, mod} =
      Emit.compile_and_load(env,
        module: String.to_atom(prefix <> Atom.to_string(canonical)),
        functions: locals,
        prefix: prefix,
        local_owners: [owner]
      )

    mod
  end

  # A per-test module-name prefix, sanitized into a valid atom segment.
  defp prefix_for(mod) do
    seg =
      mod
      |> Atom.to_string()
      |> String.replace_prefix("Elixir.", "")
      |> String.replace(".", "_")

    "T_" <> seg <> "."
  end

  test "Std.Option runs correctly with the dependent constructor representation" do
    m = load_std("option")
    # `Std.Option` exposes no `some`/`none` wrappers — `Some`/`None` are the
    # constructors and erase inline — so the erased terms are written directly
    # here. `map`/`filter` cover the CONSTRUCTION side of the representation
    # (their bodies build `Some(...)` / `None()`), `is_some`/`unwrap` the
    # matching side.
    some = {:some, 42}
    none = :none

    assert apply(m, :is_some, [some]) == true
    assert apply(m, :is_none, [none]) == true
    assert apply(m, :unwrap, [some, 0]) == 42
    assert apply(m, :unwrap, [none, 99]) == 99
    assert apply(m, :map, [some, fn x -> x * 2 end]) == {:some, 84}
    assert apply(m, :map, [none, fn x -> x * 2 end]) == :none
    assert apply(m, :filter, [some, fn x -> x > 100 end]) == :none
  end

  test "Std.Result runs correctly with the dependent constructor representation" do
    m = load_std("result")
    ok = apply(m, :ok, [7])
    err = apply(m, :error, [:bad])

    assert ok == {:ok, 7}
    assert err == {:error, :bad}
    assert apply(m, :is_ok, [ok]) == true
    assert apply(m, :is_error, [err]) == true
    assert apply(m, :unwrap, [ok, 0]) == 7
    assert apply(m, :unwrap, [err, 0]) == 0
  end

  test "Std.Math (pure @extern surface) runs correctly via the dependent emitter" do
    m = load_std("math")
    assert apply(m, :abs, [-5]) == 5
    assert apply(m, :max, [3, 7]) == 7
    assert apply(m, :min, [3, 7]) == 3
  end

  test "Std.List (recursion + list externs) runs correctly via the dependent emitter" do
    m = load_std("list")
    assert apply(m, :length, [[1, 2, 3]]) == 3
    assert apply(m, :reverse, [[1, 2, 3]]) == [3, 2, 1]
  end

  test "Std.Bool (boolean logic) runs correctly via the dependent emitter" do
    m = load_std("bool")
    assert apply(m, :and, [true, false]) == false
    assert apply(m, :and, [true, true]) == true
    assert apply(m, :not, [false]) == true
  end
end
