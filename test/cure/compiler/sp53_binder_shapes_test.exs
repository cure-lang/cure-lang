# test/cure/compiler/sp53_binder_shapes_test.exs
#
# SP5.3 Task-0 grounding: pin the exact parser AST shapes the auto-hygiene
# scope-aware walk depends on. These are CHARACTERIZATION assertions — they lock
# the binder-position tuples described in the SP5.3 plan (§2/§4) so that a later
# parser change which alters a binder shape breaks HERE (a clear, local signal)
# rather than silently mis-scoping a rename frame in the hygiene walk.
#
# Each test names the plan's IN/OUT-set claim it locks. If one goes red, the walk
# in parser.ex must be reconciled with the new shape before trusting its frames.
defmodule Cure.Compiler.SP53BinderShapesTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.MetaAST.Metadata

  defp parse(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)

    with {:ok, ast} <- Parser.parse(tokens, emit_events: false),
         do: {:ok, Metadata.strip_diagnostics(ast)}
  end

  # Body AST of a single-clause fn `name` (`{:function_def, meta, [body]}`).
  defp fn_body({:function_def, meta, [body]}, name),
    do: if(to_string(Keyword.get(meta, :name)) == name, do: body)

  defp fn_body({_t, _m, ch}, name) when is_list(ch), do: Enum.find_value(ch, &fn_body(&1, name))
  defp fn_body(_, _), do: nil

  # Whole `{:function_def, meta, children}` node for `name` (any clause shape).
  defp fn_node({:function_def, meta, _} = n, name),
    do: if(to_string(Keyword.get(meta, :name)) == name, do: n)

  defp fn_node({_t, _m, ch}, name) when is_list(ch), do: Enum.find_value(ch, &fn_node(&1, name))
  defp fn_node(_, _), do: nil

  defp body_of(src, name) do
    {:ok, ast} = parse(src)
    fn_body(ast, name)
  end

  defp node_of(src, name) do
    {:ok, ast} = parse(src)
    fn_node(ast, name)
  end

  # ---- IN set (renamable — proper tuples/keyword-lists, real-AST scope body) ----

  test "expr-form let: LHS variable binds, scope is the body sibling (§4 IN)" do
    body = body_of("mod M\n  fn f(g: Int) -> Int = let x = 1 in x + g\n", "f")

    assert {:block, _, [assign, tail]} = body
    assert {:assignment, meta, [{:variable, _, "x"}, {:literal, _, 1}]} = assign
    assert Keyword.get(meta, :let) == true
    # the body sibling references the binder `x` and the free `g`
    assert {:binary_op, _, [{:variable, _, "x"}, {:variable, _, "g"}]} = tail
  end

  test "constructor-pattern let: LHS-leaf binds, RHS is a reference (SERIOUS 2, §4 IN)" do
    body = body_of("mod M\n  fn f(p: Int) -> Int = let Some(x) = p in x\n", "f")

    assert {:block, _, [assign, {:variable, _, "x"}]} = body
    # binder = the {:variable} LEAF of the LHS constructor pattern (first child)
    assert {:assignment, _, [lhs, rhs]} = assign
    assert {:function_call, lhs_meta, [{:variable, _, "x"}]} = lhs
    assert Keyword.fetch!(lhs_meta, :name) == "Some"
    # RHS is an outer reference/hole, NOT a binder
    assert {:variable, _, "p"} = rhs
  end

  test "block-form let (no in): assignment scopes the FOLLOWING sibling (§4 IN)" do
    body = body_of("mod M\n  fn f(a: Int) -> Int =\n    let tmp = 0\n    tmp + a\n", "f")

    assert {:block, _, [assign, sibling]} = body
    assert {:assignment, _, [{:variable, _, "tmp"}, {:literal, _, 0}]} = assign
    # the binder scopes the following sibling, not a nested body
    assert {:binary_op, _, [{:variable, _, "tmp"}, {:variable, _, "a"}]} = sibling
  end

  test "nested-shadow let: inner block re-binds the same name (shadowing frame)" do
    body = body_of("mod M\n  fn f() -> Int = let x = 1 in let x = 2 in x\n", "f")

    assert {:block, _, [outer_assign, inner_block]} = body
    assert {:assignment, _, [{:variable, _, "x"}, {:literal, _, 1}]} = outer_assign
    assert {:block, _, [inner_assign, {:variable, _, "x"}]} = inner_block
    assert {:assignment, _, [{:variable, _, "x"}, {:literal, _, 2}]} = inner_assign
  end

  test "expr-position lambda: params in meta keyword-list, real-AST body (§4 IN)" do
    body = body_of("mod M\n  fn f(xs: Int) -> Int = map(fn(y) -> y + 1)\n", "f")

    assert {:function_call, _, [lambda]} = body
    assert {:lambda, meta, [lam_body]} = lambda
    # params: is a meta list of {:param, _, string} tuples (string child = binder)
    assert [{:param, _, "y"}] = Keyword.get(meta, :params)
    assert {:binary_op, _, [{:variable, _, "y"}, {:literal, _, 1}]} = lam_body
  end

  test "match arm: pattern in meta, guard in meta, both scope [body] (§4 IN, MINOR 1 guard)" do
    body =
      body_of(
        "mod M\n  fn f(o: Int) -> Int = match o\n    Some(x) when x > 0 -> x\n    None -> 0\n",
        "f"
      )

    assert {:pattern_match, _, [_scrut, arm | _]} = body
    assert {:match_arm, arm_meta, [{:variable, _, "x"}]} = arm
    # pattern leaf `x` is a binder; guard references it — both must be in the frame
    assert {:function_call, [{:name, "Some"} | _], [{:variable, _, "x"}]} =
             Keyword.get(arm_meta, :pattern)

    assert {:binary_op, _, [{:variable, _, "x"}, {:literal, _, 0}]} =
             Keyword.get(arm_meta, :guard)
  end

  test "comprehension: generator pattern is a CHILD scoping the EARLIER-sibling body (MINOR 2 reverse-scope)" do
    body = body_of("mod M\n  fn f(src: Int) -> Int = [x + 1 for x <- src]\n", "f")

    # body is the FIRST child; the generator follows it as a later sibling
    assert {:comprehension, _, [comp_body, generator | _]} = body
    assert {:binary_op, _, [{:variable, _, "x"}, {:literal, _, 1}]} = comp_body
    # generator = {:generator, [], [pattern, collection]}: pattern first child (binder),
    # collection second child (reference). The binder scopes the earlier body sibling.
    assert {:generator, _, [{:variable, _, "x"}, {:variable, _, "src"}]} = generator
  end

  test "single-clause fn-def: guards/return_type/constraints in meta reference params (SERIOUS 1)" do
    guarded = node_of("mod M\n  fn g(x: Int) when x > 0 = x + 1\n", "g")
    assert {:function_def, gmeta, [_body]} = guarded
    assert {:binary_op, _, [{:variable, _, "x"}, {:literal, _, 0}]} = Keyword.get(gmeta, :guards)
    assert [{:param, _, "x"}] = Keyword.get(gmeta, :params)

    dependent = node_of("mod M\n  fn g(n: Nat) -> Vec(n) = mk(n)\n", "g")
    assert {:function_def, dmeta, [_body]} = dependent

    assert {:function_call, [{:name, "Vec"} | _], [{:variable, _, "n"}]} =
             Keyword.get(dmeta, :return_type)

    where = node_of("mod M\n  fn g(x: Int) where Foo(x) = x\n", "g")
    assert {:function_def, wmeta, [_body]} = where

    assert [{:function_call, [{:name, "Foo"} | _], [{:variable, _, "x"}]}] =
             Keyword.get(wmeta, :constraints)
  end

  # ---- OUT set (must stay a no-op) ----

  test "multi-clause fn-def: EMPTY children + walkable params: in meta (MINOR 1 boundary)" do
    node = node_of("mod M\n  fn g(x: Int) -> Int\n    | 0 -> 1\n    | n -> n\n", "g")

    # The single-child [body] discriminator is what keeps the walk off this node:
    # children are EMPTY, so a frame matching strictly on {:function_def, _, [body]}
    # never fires here — even though params: (the signature) IS a walkable tuple list.
    assert {:function_def, meta, []} = node
    assert [{:param, _, "x"}] = Keyword.get(meta, :params)
    # clauses live in raw maps (never walked by the tuple/list-only recursion)
    assert [%{params: _, body: _} | _] = Keyword.get(meta, :clauses)
  end
end
