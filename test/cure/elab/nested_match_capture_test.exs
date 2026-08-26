defmodule Cure.Elab.NestedMatchCaptureTest do
  @moduledoc """
  Two nested `match`es, each scrutinising a value with a NESTED constructor
  pattern (`Some(Y(x, r))`), where the innermost body references a variable
  bound by the OUTER match's nested pattern, must elaborate.

  The nested-pattern desugarer (`compile_group`/`split_ctor_arms`) lowered a
  nested pattern to a tree of single-level matches over FRESH scrutinee names
  derived deterministically from the outer constructor: `Some(Y(x, r))` became
  `Some($nSome1) -> match $nSome1 | Y($nSome1_Y1, $nSome1_Y2) -> …`, renaming
  `x` to `$nSome1_Y1` in the body. Because the names were seeded only from the
  constructor (not made unique per invocation), the INNER match — desugared
  independently — regenerated the SAME `$nSome1_Y1` for its own binder and
  shadowed the outer one. The outer `x` reference was captured by the inner
  binder (a different type), so the body failed `:branch_type`.

  Giving each desugaring invocation a unique seed removes the capture. This is
  the residual blocker that kept `Std.Iter` (`zip_with`) off the dependent
  pipeline.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  test "inner match body references outer nested-pattern binder" do
    src = """
    mod M
      use Std.Option
      type W(a) = Y(a, a)
      fn f(a: Option(W(t)), b: Option(W(u))) -> Option(t) =
        match a
          None() -> None()
          Some(Y(x, ra)) ->
            match b
              None() -> None()
              Some(Y(y, rb)) -> Some(x)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "let-bound nested-match lambda referencing outer binder (Std.Iter zip_with shape, non-curried)" do
    # The `let next = fn(_) -> nested match … outer-bound var …` shape used
    # throughout Std.Iter.
    src = """
    mod M
      use Std.Option
      type StepToken = Step
      type Iter(a) = Iter(StepToken -> Option(IterStep(a)))
      type IterStep(a) = Yield(a, Iter(a))
      local fn step(it: Iter(t)) -> Option(IterStep(t)) =
        match it
          Iter(next) -> next(Step())
      fn zip_first(a: Iter(t), b: Iter(u)) -> Iter(t) =
        let next = fn(_) ->
          match step(a)
            None() -> None()
            Some(Yield(x, rest_a)) ->
              match step(b)
                None() -> None()
                Some(Yield(y, rest_b)) -> Some(Yield(x, zip_first(rest_a, rest_b)))
        Iter(next)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "nested-pattern binder used inside a CURRIED application (Std.Iter zip_with, f(x)(y))" do
    # zip_with's real shape: `f : t -> u -> v` combines the two elements via the
    # curried application `f(x)(y)`, where `x` is bound by the OUTER match's
    # nested pattern. A curried call `f(x)` parses with its callee preserved in
    # the node's META (`callee:`), NOT its children (parser.ex `parse_call`).
    # The nested-pattern desugarer renames `x` to a fresh scrutinee name via
    # `subst_surface_var`, which walked children only — so the `x` hidden inside
    # the callee `f(x)` was never renamed and leaked to the kernel as
    # `{:global, :x}` → `:unknown_global`. Substituting through `:callee` fixes
    # it. This was Std.Iter's last blocker.
    src = """
    mod M
      use Std.Option
      type StepToken = Step
      type Iter(a) = Iter(StepToken -> Option(IterStep(a)))
      type IterStep(a) = Yield(a, Iter(a))
      local fn step(it: Iter(t)) -> Option(IterStep(t)) =
        match it
          Iter(next) -> next(Step())
      fn zip_with(a: Iter(t), b: Iter(u), f: t -> u -> v) -> Iter(v) =
        let next = fn(_) ->
          match step(a)
            None() -> None()
            Some(Yield(x, rest_a)) ->
              match step(b)
                None() -> None()
                Some(Yield(y, rest_b)) -> Some(Yield(f(x)(y), zip_with(rest_a, rest_b, f)))
        Iter(next)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a branch binder shadowing a nested-pattern variable gets exact source roles" do
    src = """
    mod N
      type Nat = Z | S(Nat)
      fn f(x: Nat) -> Nat = match x
        S(S(n)) ->
          let g : (Nat) -> Nat = fn(n) -> n
          g(n)
        S(Z()) -> Z()
        Z() -> Z()
    end
    """

    assert {:error,
            {:source_context, {:unsupported_pattern, %{reason: :shadowed_nested, name: "n", shadow_span: shadow_span}},
             _} = error} =
             Program.elaborate(src)

    assert shadow_span.start_line == 5
    assert shadow_span.start_column == 33

    {diagnostic, registry} = Errors.to_diagnostic(error, "nested_shadow.cure", src)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- NESTED PATTERN SHADOWS `N` [E090] ------------------------ nested_shadow.cure

             This nested constructor pattern binds `n`. A binder inside its branch uses the
             same name, so lowering the nested pattern could capture the inner value.

             at nested_shadow.cure:5:33
             4 |     S(S(n)) ->
               |     ------- this nested pattern is lowered before its branch is checked
               |         - this outer pattern binds `n`
             5 |       let g : (Nat) -> Nat = fn(n) -> n
               |                                 ^ rename this inner binder so it does not shadow `n`

             Hint: Give the nested binder a different name and update its branch body
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 4, "character" => 32},
             "end" => %{"line" => 4, "character" => 33}
           }

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             %{
               "start" => %{"line" => 3, "character" => 8},
               "end" => %{"line" => 3, "character" => 9}
             },
             %{
               "start" => %{"line" => 3, "character" => 4},
               "end" => %{"line" => 3, "character" => 11}
             }
           ]

    assert lsp["data"]["payload"] == %{
             "checking" => "f",
             "kind" => "unsupported_pattern",
             "name" => "n",
             "reason" => "shadowed_nested"
           }

    fixed = String.replace(src, "fn(n) -> n", "fn(value) -> value")
    assert {:ok, _environment} = Program.elaborate(fixed, file: "nested_shadow_fixed.cure")
  end
end
