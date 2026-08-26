defmodule Cure.Elab.SemigroupConcatTest do
  @moduledoc """
  Concatenation is an operator overload resolved through the `Std.Semigroup`
  interface — not a bespoke case in `build_binop`. `<>` desugars to the
  `combine` method, and `+` on a non-numeric operand desugars to the same
  (Swift-style `+` overload), so both dispatch by coherence to the `List`
  implementation (which delegates to the reducing library `Std.List.append`).
  `String` is a nominal record rather than a `List(Char)` alias, so it carries
  its own instance and concatenation returns a `String`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  defp eval(src, fname, mod) do
    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [fname])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, fname, [])
  end

  test "`<>` on lists dispatches to Semigroup.combine and appends" do
    src = """
    mod T
      use Std.Semigroup
      use Std.List
      fn go() -> List(Int) = [1, 2] <> [3, 4]
    end
    """

    assert eval(src, :go, :"Cure.SgAngle") == [1, 2, 3, 4]
  end

  test "`+` on lists is the Semigroup overload (Swift-style) and appends" do
    src = """
    mod T
      use Std.Semigroup
      use Std.List
      fn go() -> List(Int) = [1, 2] + [3, 4]
    end
    """

    assert eval(src, :go, :"Cure.SgPlus") == [1, 2, 3, 4]
  end

  test "`<>` on strings concatenates through String's own Semigroup instance" do
    src = """
    mod T
      use Std.Semigroup
      use Std.String
      fn go() -> String = "ab" <> "cd"
    end
    """

    # `{:String, charlist}` is the erasure of the nominal record, not a stray
    # wrapper: `String` owns its `Semigroup` instance now rather than borrowing
    # `List`'s, so the result is a `String` and stays one.
    assert eval(src, :go, :"Cure.SgStr") == {:String, ~c"abcd"}
  end

  test "a nested concat needs no `use Std.Semigroup`" do
    # This used to assert `operator_provider_not_in_scope`. That guard can no
    # longer fire for `<>`: instance coherence is global, and `Std.String` is
    # `@prelude` and carries `implementation Semigroup for String`, so `combine`
    # has a meaning in every module whether or not `Std.Semigroup` is used.
    # (`Std.Semigroup`'s own `List` instance rides along for the same reason —
    # instances are global, not import-scoped.)
    assert {:ok, _env} =
             Program.elaborate("mod T\n  fn go() -> String = \"a\" <> \"b\" <> \"c\"\n",
               file: "ambient_semigroup.cure"
             )
  end

  test "the missing-provider diagnostic names the operator, the method and the fix" do
    # The guard is unreachable for `<>` today (see above) but is not dead: it is
    # the general answer for an operator whose provider a module has not brought
    # into scope. Render it from the reason so the wording and the caret
    # placement stay covered by the suite rather than only by the code path that
    # currently cannot produce it.
    src = "mod T\n  fn go() -> String = \"a\" <> \"b\" <> \"c\"\n"

    span = %Cure.Diagnostic.Span{
      source_id: "missing_semigroup.cure",
      path: "missing_semigroup.cure",
      start_byte: 34,
      end_byte: 36,
      start_line: 2,
      start_column: 27,
      end_line: 2,
      end_column: 29
    }

    reason =
      {:source_context,
       {:operator_provider_not_in_scope, %{operator: :<>, method: :combine, provider: "Std.Semigroup"}},
       %{span: span, checking: :go}}

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(reason, "missing_semigroup.cure", src)

    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry)
    assert rendered =~ "OPERATOR PROVIDER IS NOT IN SCOPE"
    assert rendered =~ "`<>` operator dispatches through `Std.Semigroup.combine/2`"
    assert rendered =~ "add `use Std.Semigroup` to this module"
    assert rendered =~ ~r/2 \|   fn go\(\) -> String = "a" <> "b" <> "c"\n\s+\|\s+\^\^/
  end

  test "numeric `+` and `<` are untouched by the overload" do
    assert eval("mod T\n  fn go() -> Int = 2 + 3\nend\n", :go, :"Cure.SgNumAdd") == 5
    assert eval("mod T\n  fn go() -> Bool = 2 < 3\nend\n", :go, :"Cure.SgNumLt") == true
  end

  # Regression: the generated `combine` List instance lowers its body to a
  # `case Arg of [H|T] -> … ; [] -> … end`. The cons-pattern binders `H`/`T`
  # come from `fresh_var("V")` = `V<unique_integer>`, while the function's own
  # parameters are positional `V<pos>` (small de Bruijn indices). Because
  # `System.unique_integer/1` can hand back a *small* value early in the VM's
  # life, a fresh binder could mint the exact name `V1`/`V2` already in scope as
  # a parameter — turning a fresh cons-bind into an equality match against the
  # whole list and crashing at runtime (a non-deterministic `CaseClauseError`,
  # seeded by VM state). The invariant that rules this out: a synthetic binder
  # must never take the reserved positional shape `V<digits>`. Checking the
  # *shape* (not a specific collision) makes this deterministic regardless of
  # the counter's current value.
  test "synthetic case-pattern binders never take the reserved positional shape" do
    src = """
    mod T
      use Std.Semigroup
      use Std.List
      fn go() -> List(Int) = [1, 2] <> [3, 4]
    end
    """

    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [:go])
    {:ok, forms} = Emit.compile_forms(env, :"Cure.SgShape", fns)

    offenders = Enum.flat_map(forms, &case_pattern_vars/1)

    assert Enum.filter(offenders, &(&1 =~ ~r/^V\d+$/)) == [],
           "case-pattern binders with the reserved positional shape V<digits>: " <>
             inspect(Enum.uniq(offenders))
  end

  # Variable names bound in the PATTERN position of any `case` clause, gathered
  # recursively (nested cases included). Function-head parameters are the
  # top-level clause params and are *not* reached here.
  defp case_pattern_vars({:case, _l, scrut, clauses}) do
    from_clauses =
      Enum.flat_map(clauses, fn {:clause, _cl, patterns, _guards, body} ->
        Enum.flat_map(patterns, &pattern_vars/1) ++ Enum.flat_map(body, &case_pattern_vars/1)
      end)

    case_pattern_vars(scrut) ++ from_clauses
  end

  defp case_pattern_vars(form) when is_tuple(form),
    do: Enum.flat_map(Tuple.to_list(form), &case_pattern_vars/1)

  defp case_pattern_vars(form) when is_list(form), do: Enum.flat_map(form, &case_pattern_vars/1)
  defp case_pattern_vars(_), do: []

  defp pattern_vars({:var, _l, name}), do: [Atom.to_string(name)]
  defp pattern_vars({:cons, _l, h, t}), do: pattern_vars(h) ++ pattern_vars(t)
  defp pattern_vars({:tuple, _l, elts}), do: Enum.flat_map(elts, &pattern_vars/1)
  defp pattern_vars(_), do: []

  test "`<>` in checking position (a call argument) dispatches" do
    # The concat operator must resolve when it appears in checking mode, not
    # only as a whole function body — here as the argument of `length`, checked
    # against its `List(Int)` parameter.
    src = """
    mod T
      use Std.Semigroup
      use Std.List
      fn go() -> Int = length([1, 2] <> [3])
    end
    """

    assert eval(src, :go, :"Cure.SgChecked") == 3
  end
end
