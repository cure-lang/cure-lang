defmodule Cure.Elab.TuplePatternTest do
  @moduledoc """
  Parity row #4 (non-constructor patterns) — tuple/pair patterns. A Σ/pair is
  irrefutable, so a single `%[x, y] -> body` arm is a destructure, not a coverage
  problem. `try_tuple_match` lowers it to the already-supported projections:
  `body[x ↦ p.1, y ↦ p.2]` (Core `{:fst}`/`{:snd}` on the elaborated variable
  scrutinee), so no `{:vdata}` scrutinee and no new eliminator is needed.
  Refutable tuple positions are lowered to nested matches over those same
  projections, preserving constructor coverage and source diagnostics. Oracle
  `match/mt13_tuple_pattern` pins accept/accept parity.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Emit, Program}

  @nat "mod M\n  type Nat = Z | S(Nat)\n"

  test "a tuple pattern binds both projections and runs on the BEAM" do
    src = @nat <> "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n    %[x, y] -> S(y)\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.TuplePatternE2E", functions: [:f])

    # Runtime pair is a 2-tuple {a, b}; `.1`/`.2` are element(1)/element(2).
    assert apply(mod, :f, [{:Z, {:S, :Z}}]) == {:S, {:S, :Z}}
    assert apply(mod, :f, [{{:S, :Z}, :Z}]) == {:S, :Z}
  end

  test "the first projection is bound correctly" do
    src = @nat <> "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n    %[x, y] -> x\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.TuplePatternFstE2E", functions: [:f])

    assert apply(mod, :f, [{:Z, {:S, :Z}}]) == :Z
  end

  test "a wildcard tuple element drops its projection" do
    src = @nat <> "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n    %[_, y] -> y\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a branch binder shadowing a tuple element gets exact source roles" do
    src =
      @nat <>
        "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n" <>
        "    %[x, y] ->\n      let g : (Nat) -> Nat = fn(x) -> x\n      g(y)\nend\n"

    assert {:error,
            {:source_context, {:unsupported_pattern, %{reason: :shadowed_tuple, name: "x", shadow_span: shadow_span}},
             _} = error} =
             Program.elaborate(src)

    assert shadow_span.start_line == 5
    assert shadow_span.start_column == 33

    {diagnostic, registry} = Errors.to_diagnostic(error, "tuple_shadow.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NESTED PATTERN SHADOWS `X` [E090] ------------------------- tuple_shadow.cure

             This tuple pattern binds `x` to one of the tuple's positions. A binder inside
             the branch uses the same name, so substituting the projection could capture the
             inner value.

             at tuple_shadow.cure:5:33
             4 |     %[x, y] ->
               |     ------- this tuple pattern is projected before its branch is checked
               |       - this outer pattern binds `x`
             5 |       let g : (Nat) -> Nat = fn(x) -> x
               |                                 ^ rename this inner binder so it does not shadow `x`

             Hint: Give the nested binder a different name and update its branch body
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 4, "character" => 32},
             "end" => %{"line" => 4, "character" => 33}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             %{
               "start" => %{"line" => 3, "character" => 6},
               "end" => %{"line" => 3, "character" => 7}
             },
             %{
               "start" => %{"line" => 3, "character" => 4},
               "end" => %{"line" => 3, "character" => 11}
             }
           ]

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_pattern",
             "name" => "x",
             "reason" => "shadowed_tuple"
           }

    fixed = String.replace(src, "fn(x) -> x", "fn(value) -> value")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "tuple_shadow_fixed.cure")
  end

  test "a lone catch-all arm works on a pair scrutinee (any scrutinee type)" do
    # `_` ignores the scrutinee's structure, so a Σ scrutinee needs no vdata
    # dispatch; the scrutinee is still elaborated for well-typedness.
    src = @nat <> "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n    _ -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PairCatchallE2E", functions: [:f])

    assert apply(mod, :f, [{:S, :Z}]) == :Z
  end

  test "a named catch-all binds the whole pair scrutinee" do
    src =
      @nat <>
        "  fn f(p: Sigma(a: Nat, Nat)) -> Sigma(a: Nat, Nat) = match p\n    w -> w\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PairNamedCatchallE2E", functions: [:f])

    assert apply(mod, :f, [{:S, :Z}]) == {:S, :Z}
  end

  test "an ill-typed scrutinee under a catch-all is still rejected" do
    src = @nat <> "  fn f(n: Nat) -> Nat = match undefined_thing\n    _ -> Z()\nend\n"

    assert {:error, _} = Program.elaborate(src)
  end

  test "a tuple pattern inside a constructor argument destructures the Σ field" do
    # `A(%[x, y])` becomes `A($tup_0)` with `x ↦ $tup_0.1`, `y ↦ $tup_0.2`.
    src =
      @nat <>
        "  type T = A(Sigma(a: Nat, Nat)) | B\n  fn f(t: T) -> Nat = match t\n    A(%[x, y]) -> y\n    B() -> Z()\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.TupleInCtorE2E", functions: [:f])

    assert apply(mod, :f, [{:A, {:Z, {:S, :Z}}}]) == {:S, :Z}
    assert apply(mod, :f, [:B]) == :Z
  end

  test "a constructor's refutable tuple field is lowered, exhaustive, and runs" do
    src =
      @nat <>
        "  type T = A(Sigma(a: Nat, Nat)) | B\n" <>
        "  fn f(t: T) -> Nat = match t\n" <>
        "    A(%[S(x), y]) -> x\n" <>
        "    A(%[Z(), y]) -> y\n" <>
        "    B() -> Z()\n" <>
        "end\n"

    {:ok, environment} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(environment, module: :"Cure.RefutableConstructorTupleE2E", functions: [:f])

    assert apply(mod, :f, [{:A, {{:S, {:S, :Z}}, :Z}}]) == {:S, :Z}
    assert apply(mod, :f, [{:A, {:Z, {:S, :Z}}}]) == {:S, :Z}
    assert apply(mod, :f, [:B]) == :Z
  end

  test "tuple and constructor columns compose in the same pattern matrix" do
    src =
      @nat <>
        "  type T = A(Nat, Sigma(a: Nat, Nat)) | B\n" <>
        "  fn f(t: T) -> Nat = match t\n" <>
        "    A(S(x), %[S(y), z]) -> x\n" <>
        "    A(S(x), %[Z(), z]) -> z\n" <>
        "    A(Z(), %[y, z]) -> y\n" <>
        "    B() -> Z()\n" <>
        "end\n"

    {:ok, environment} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(environment, module: :"Cure.MixedTupleMatrixE2E", functions: [:f])

    assert apply(mod, :f, [{:A, {:S, {:S, :Z}}, {{:S, :Z}, :Z}}]) == {:S, :Z}
    assert apply(mod, :f, [{:A, {:S, :Z}, {:Z, {:S, :Z}}}]) == {:S, :Z}
    assert apply(mod, :f, [{:A, :Z, {{:S, :Z}, :Z}}]) == {:S, :Z}
    assert apply(mod, :f, [:B]) == :Z
  end

  test "a constructor tuple field reports its missing inner constructor at the authored pattern" do
    src =
      @nat <>
        "  type T = A(Sigma(a: Nat, Nat)) | B\n" <>
        "  fn f(t: T) -> Nat = match t\n" <>
        "    A(%[S(x), y]) -> x\n" <>
        "    B() -> Z()\n" <>
        "end\n"

    assert {:error,
            {:source_context,
             {:tuple_missing_branch,
              %{
                branch: :"M#Z",
                tuple_pattern_position: 1,
                tuple_pattern_insertion_span: insertion_span
              }}, _} = error} = Program.elaborate(src)

    assert {insertion_span.start_line, insertion_span.start_column} == {5, 23}

    {diagnostic, registry} = Errors.to_diagnostic(error, "constructor_tuple_gap.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TUPLE PATTERN IS MISSING `Z` IN POSITION 1 [E118] -- constructor_tuple_gap.cure

             The value in tuple position 1 can be `Z`, but no tuple branch handles that
             constructor there.

             at constructor_tuple_gap.cure:5:23
             5 |     A(%[S(x), y]) -> x
               |         ----          ^ this tuple position handles another constructor here; add a tuple branch with `Z` in position 1

             Hint: Add `%[Z(...), _] -> ...`, or a tuple catch-all branch
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 4, "character" => 22},
             "end" => %{"line" => 4, "character" => 22}
           }

    assert [related] = lsp["relatedInformation"]

    assert related["location"]["range"] == %{
             "start" => %{"line" => 4, "character" => 8},
             "end" => %{"line" => 4, "character" => 12}
           }

    assert lsp["data"]["payload"] == %{
             "branch" => "M#Z",
             "checking" => "f",
             "kind" => "missing_branch",
             "position" => 1
           }

    fixed = String.replace(src, "    A(%[S(x), y]) -> x\n", "    A(%[S(x), y]) -> x\n    A(%[Z(), y]) -> y\n")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "constructor_tuple_gap_fixed.cure")
  end

  test "a branch binder shadowing a constructor's tuple element gets exact source roles" do
    src =
      @nat <>
        "  type T = A(Sigma(a: Nat, Nat)) | B\n" <>
        "  fn f(t: T) -> Nat = match t\n" <>
        "    A(%[x, y]) ->\n      let g : (Nat) -> Nat = fn(x) -> x\n      g(y)\n    B() -> Z()\nend\n"

    assert {:error,
            {:source_context,
             {:unsupported_pattern, %{reason: :shadowed_tuple_arg, name: "x", shadow_span: shadow_span}}, _} = error} =
             Program.elaborate(src)

    assert shadow_span.start_line == 6
    assert shadow_span.start_column == 33

    {diagnostic, registry} = Errors.to_diagnostic(error, "tuple_arg_shadow.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NESTED PATTERN SHADOWS `X` [E090] --------------------- tuple_arg_shadow.cure

             This tuple pattern inside a constructor binds `x` to one of the field's
             positions. A binder inside the branch uses the same name, so substituting the
             projection could capture the inner value.

             at tuple_arg_shadow.cure:6:33
             5 |     A(%[x, y]) ->
               |       ------- this constructor field is destructured as a tuple
               |         - this outer pattern binds `x`
             6 |       let g : (Nat) -> Nat = fn(x) -> x
               |                                 ^ rename this inner binder so it does not shadow `x`

             Hint: Give the nested binder a different name and update its branch body
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 5, "character" => 32},
             "end" => %{"line" => 5, "character" => 33}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             %{
               "start" => %{"line" => 4, "character" => 8},
               "end" => %{"line" => 4, "character" => 9}
             },
             %{
               "start" => %{"line" => 4, "character" => 6},
               "end" => %{"line" => 4, "character" => 13}
             }
           ]

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_pattern",
             "name" => "x",
             "reason" => "shadowed_tuple_arg"
           }

    fixed = String.replace(src, "fn(x) -> x", "fn(value) -> value")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "tuple_arg_shadow_fixed.cure")
  end

  test "a plain constructor match is unaffected by the tuple path" do
    src = @nat <> "  fn f(n: Nat) -> Nat = match n\n    S(m) -> m\n    Z() -> Z()\nend\n"

    assert {:ok, _} = Program.elaborate(src)
  end

  test "a pair literal is constructible as a function argument and matches end-to-end" do
    # Previously `%[…]` in inference position was `:unsupported_expression`; the
    # pair now lowers to the inductive Core `{:ctor, :mk_pair, …}` (D2) and the
    # kernel types the application by checking it against the callee's Σ domain.
    src =
      @nat <>
        "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n    %[x, y] -> y\n" <>
        "  fn g() -> Nat = f(%[Z(), S(Z())])\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.PairCtorE2E", functions: [:f, :g])

    # g constructs %[Z, S(Z)] and f returns its second component.
    assert apply(mod, :g, []) == {:S, :Z}
  end

  test "an n-element flat-telescope tuple pattern projects positionally" do
    # Option B: a flat `%[x, y, z]` pattern matches a flat `Tuple(…)` telescope
    # (unit-terminated Σ, lowered to a flat BEAM tuple), binding each component
    # POSITIONALLY (`x = p.1`, `y = p.2`, `z = p.3`). A genuinely nested Σ is
    # destructured with the nested pattern `%[x, %[y, z]]` instead (see below).
    src =
      @nat <>
        "  fn f(p: Tuple(Nat, Nat, Nat)) -> Nat = match p\n    %[x, y, z] -> z\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.TripleTupleE2E", functions: [:f])

    # p = {Z, S Z, S(S Z)} (flat); the third element is p.3.
    assert apply(mod, :f, [{:Z, {:S, :Z}, {:S, {:S, :Z}}}]) == {:S, {:S, :Z}}
  end

  test "tuple pattern arity is checked even when extra or missing binders are unused" do
    too_few = @nat <> "  fn f(p: Tuple(Nat, Nat)) -> Nat = match p\n    %[x] -> Z()\nend\n"
    too_many = @nat <> "  fn f(p: Tuple(Nat, Nat)) -> Nat = match p\n    %[x, y, z] -> Z()\nend\n"

    assert {:error, {:source_context, {:tuple_arity_mismatch, 2, 1}, %{span: %Cure.Diagnostic.Span{}}}} =
             Program.elaborate(too_few)

    assert {:error, {:source_context, {:tuple_arity_mismatch, 2, 3}, %{span: %Cure.Diagnostic.Span{}}}} =
             Program.elaborate(too_many)
  end

  test "a nested tuple pattern binds through the inner Σ" do
    src =
      @nat <>
        "  fn f(p: Sigma(a: Nat, Sigma(b: Nat, Nat))) -> Nat = match p\n    %[x, %[y, z]] -> y\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.NestedTupleE2E", functions: [:f])

    # y is the first component of the inner pair, i.e. p.2.1.
    assert apply(mod, :f, [{:Z, {{:S, :Z}, {:S, {:S, :Z}}}}]) == {:S, :Z}
  end

  test "constructor patterns inside a tuple are exhaustive and run on the BEAM" do
    src =
      @nat <>
        "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n" <>
        "    %[S(x), y] -> x\n" <>
        "    %[Z(), y] -> y\n" <>
        "  fn g(p: Sigma(a: Nat, Nat)) -> Nat = match p\n" <>
        "    %[x, S(y)] -> y\n" <>
        "    %[x, Z()] -> x\n" <>
        "end\n"

    {:ok, environment} = Program.elaborate(src)

    {:ok, mod} =
      Emit.compile_and_load(environment, module: :"Cure.RefutableTupleE2E", functions: [:f, :g])

    assert apply(mod, :f, [{{:S, {:S, :Z}}, :Z}]) == {:S, :Z}
    assert apply(mod, :f, [{:Z, {:S, :Z}}]) == {:S, :Z}
    assert apply(mod, :g, [{:Z, {:S, {:S, :Z}}}]) == {:S, :Z}
    assert apply(mod, :g, [{{:S, :Z}, :Z}]) == {:S, :Z}
  end

  test "a missing constructor in a tuple position gets a contextual branch repair" do
    src =
      @nat <>
        "  fn f(p: Sigma(a: Nat, Nat)) -> Nat = match p\n" <>
        "    %[S(x), y] -> x\n" <>
        "end\n"

    assert {:error,
            {:source_context,
             {:tuple_missing_branch,
              %{
                branch: :"M#Z",
                tuple_pattern_position: 1,
                tuple_pattern_insertion_span: insertion_span
              }}, _} = error} = Program.elaborate(src)

    assert {insertion_span.start_line, insertion_span.start_column} == {4, 20}

    {diagnostic, registry} = Errors.to_diagnostic(error, "nested_tuple_gap.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- TUPLE PATTERN IS MISSING `Z` IN POSITION 1 [E118] ----- nested_tuple_gap.cure

             The value in tuple position 1 can be `Z`, but no tuple branch handles that
             constructor there.

             at nested_tuple_gap.cure:4:20
             4 |     %[S(x), y] -> x
               |       ----         ^ this tuple position handles another constructor here; add a tuple branch with `Z` in position 1

             Hint: Add `%[Z(...), _] -> ...`, or a tuple catch-all branch
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 3, "character" => 19},
             "end" => %{"line" => 3, "character" => 19}
           }

    assert [related] = lsp["relatedInformation"]

    assert related["location"]["range"] == %{
             "start" => %{"line" => 3, "character" => 6},
             "end" => %{"line" => 3, "character" => 10}
           }

    assert lsp["data"]["payload"] == %{
             "branch" => "M#Z",
             "checking" => "f",
             "kind" => "missing_branch",
             "position" => 1
           }

    fixed = String.replace(src, "    %[S(x), y] -> x\n", "    %[S(x), y] -> x\n    %[Z(), y] -> y\n")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "nested_tuple_gap_fixed.cure")
  end

  test "a let-bound pair can be projected (Σ β-rule through substitution)" do
    # `let` is substitution-based, so `p.2` inlines to `%[Z(), S(Z())].2`, which
    # reduces to the second component directly — no pair term, no bare-pair infer.
    src =
      @nat <>
        "  fn g() -> Nat =\n    let p = %[Z(), S(Z())]\n    p.2\nend\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.LetPairProjE2E", functions: [:g])

    assert apply(mod, :g, []) == {:S, :Z}
  end
end
