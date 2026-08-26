defmodule Cure.Compiler.WithParseTest do
  @moduledoc """
  `with`-abstraction (capability A) surface parsing. `with` is a CONTEXTUAL
  keyword: it is a with-abstraction only in expression-prefix position; its
  existing FSM/actor payload-binder identifier use is unaffected.
  """
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Renderer
  alias Cure.MetaAST.Metadata

  defp parse(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    Parser.parse(toks, emit_events: false)
  end

  # Collect every {tag, meta, children} 3-tuple in the AST.
  defp collect(node, acc) do
    acc = if is_tuple(node) and tuple_size(node) == 3, do: [node | acc], else: acc

    cond do
      is_tuple(node) -> Enum.reduce(Tuple.to_list(node), acc, &collect/2)
      is_list(node) -> Enum.reduce(node, acc, &collect/2)
      true -> acc
    end
  end

  test "block-form `with e <arms>` parses to a :with_abs node" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, _meta, [scrut | arms]} = node
    assert {:variable, _, "n"} = scrut
    assert length(arms) == 2
    assert Enum.all?(arms, &match?({:match_arm, _, [_]}, &1))
  end

  test "`with e proof p <arms>` carries the proof name in meta (capability B)" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n proof pf
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, meta, [scrut | arms]} = node
    assert {:variable, _, "n"} = scrut
    assert Keyword.get(meta, :proof) == "pf"
    assert length(arms) == 2

    source_info = Metadata.source_info(meta)
    assert {source_info.fields.proof_clause.start_column, source_info.fields.proof_clause.end_column} == {12, 20}
    assert {source_info.fields.proof_keyword.start_column, source_info.fields.proof_keyword.end_column} == {12, 17}
    assert {source_info.fields.proof_name.start_column, source_info.fields.proof_name.end_column} == {18, 20}
  end

  test "`proof` after a call scrutinee is not consumed as another scrutinee" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn g(n: Nat) -> Nat = n
      fn foo(n: Nat) -> Nat =
        with g(n) proof pf
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, meta, [{:function_call, call_meta, _args} | arms]} = node
    assert Keyword.get(call_meta, :name) == "g"
    assert Keyword.get(meta, :proof) == "pf"
    assert length(arms) == 2
  end

  test "no-proof `with` leaves :proof absent in meta (capability A unchanged)" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, meta, _} = node
    assert Keyword.get(meta, :proof) == nil
  end

  # -- LHS re-matching (Idris-parity indexed views) --------------------------
  #
  # A with-clause may RESTATE the parent function's LHS patterns (refined) before
  # the with-pattern, separated by `|`:  `<parent-pat…> | <with-pat> -> body`.
  # Such an arm parses to a distinct `{:with_rematch_arm, meta, [body]}` node
  # carrying `:parent_patterns` and `:pattern` in meta. A clause WITHOUT the
  # `… |` prefix stays the ordinary no-rematch `{:match_arm}`.
  test "block-form `with` clause restating a single parent pattern parses to :with_rematch_arm" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      type NV = VZ | VS(Nat)
      fn foo(n: Nat) -> Nat =
        with view(n)
          S(m) | VS(m) -> S(m)
          Z() | VZ() -> Z()
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, _meta, [scrut | arms]} = node
    assert {:function_call, _, _} = scrut
    assert length(arms) == 2
    assert Enum.all?(arms, &match?({:with_rematch_arm, _, [_]}, &1))

    [{:with_rematch_arm, m1, [_body1]} | _] = arms
    # First arm: parent pattern `S(m)`, with-pattern `VS(m)`.
    assert [{:function_call, pm, _}] = Keyword.fetch!(m1, :parent_patterns)
    assert Keyword.get(pm, :name) == "S"
    assert {:function_call, wm, _} = Keyword.fetch!(m1, :pattern)
    assert Keyword.get(wm, :name) == "VS"
  end

  test "ordinary and rematch arms both own their complete authored ranges" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n
          Z() -> Z()
          S(m) | S(m) -> S(m)
    """

    assert {:ok, ast} = parse(src)

    {:with_abs, meta, [_scrutinee, ordinary, rematch]} =
      collect(ast, [])
      |> Enum.find(fn node -> match?({:with_abs, _, [_, _, _]}, node) end)

    outer = Metadata.source_info(meta)
    ordinary_info = ordinary |> elem(1) |> Metadata.source_info()
    rematch_info = rematch |> elem(1) |> Metadata.source_info()

    assert {outer.whole.start_line, outer.whole.end_line} == {4, 6}
    assert Enum.map(outer.branches, &{&1.start_line, &1.end_line}) == [{5, 5}, {6, 6}]
    assert {ordinary_info.whole.start_column, ordinary_info.whole.end_column} == {7, 17}
    assert {rematch_info.whole.start_column, rematch_info.whole.end_column} == {7, 26}
    assert {rematch_info.pattern.start_column, rematch_info.pattern.end_column} == {14, 18}
    assert [%{start_column: 7, end_column: 11}] = rematch_info.operands
    assert rematch_info.fields.rematch_separator.start_column == 12
    assert rematch_info.operator.start_column == 19
    assert rematch_info.body.start_column == 22
  end

  test "block-form `with` clause restating multiple (comma-sep) parent patterns" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      type NV = VZ | VS(Nat)
      fn foo(n: Nat, w: Nat) -> Nat =
        with view(n)
          S(m), w | VS(m) -> S(m)
          Z(), w | VZ() -> w
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, _meta, [_scrut | arms]} = node
    assert length(arms) == 2
    [{:with_rematch_arm, m1, _} | _] = arms
    pps = Keyword.fetch!(m1, :parent_patterns)
    assert length(pps) == 2
    assert [{:function_call, pm, _}, {:variable, _, "w"}] = pps
    assert Keyword.get(pm, :name) == "S"
  end

  test "restated parent patterns get an exact missing-bar diagnostic" do
    source = "with a\n  Z(), Z() VZ() -> 1"
    file = "with_rematch_bar.cure"
    {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(errors, &match?({:declaration_separator_missing, %{kind: :with_rematch_separator_missing}}, &1))

    assert {:declaration_separator_missing,
            %{
              kind: :with_rematch_separator_missing,
              parent_pattern_count: 2,
              observed: "VZ"
            }} = error

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, file, source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- WITH REMATCH NEEDS A BAR [E094] ----------------------- with_rematch_bar.cure

             These 2 restated parent patterns need `|` before the pattern for the `with`
             value.

             A valid continuation here starts with '|'.

             at with_rematch_bar.cure:2:12
             2 |   Z(), Z() VZ() -> 1
               |   ---  --- ^ the restated parent patterns start here; the final parent pattern ends here; insert `|` before this with-pattern

             Hint: Insert `|` before the with-pattern
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "| ", span: insertion}]}] =
             diagnostic.suggestions

    assert {insertion.start_line, insertion.start_column} == {2, 12}
    assert insertion.start_byte == insertion.end_byte

    assert [%{"newText" => "| ", "range" => edit_range}] =
             Renderer.lsp(diagnostic, registry)["data"]["suggestions"] |> hd() |> Map.fetch!("edits")

    assert edit_range == %{
             "start" => %{"line" => 1, "character" => 11},
             "end" => %{"line" => 1, "character" => 11}
           }
  end

  test "a rematch with no with-pattern gets no partial bar edit" do
    source = "with a\n  Z(), Z() -> 1"
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:error, errors} = Parser.parse(tokens, emit_events: false)

    error =
      Enum.find(errors, &match?({:declaration_separator_missing, %{kind: :with_rematch_separator_missing}}, &1))

    {diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic({:parse_error, [error]}, "nofile", source)
    assert diagnostic.suggestions == []
  end

  test "no-rematch `with` clause (no `|` prefix) stays a :match_arm" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(n: Nat) -> Nat =
        with n
          Z() -> Z()
          S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    node =
      collect(ast, [])
      |> Enum.find(fn t -> match?({:with_abs, _, [_ | _]}, t) end)

    assert {:with_abs, _meta, [_scrut | arms]} = node
    assert Enum.all?(arms, &match?({:match_arm, _, [_]}, &1))
    refute Enum.any?(arms, &match?({:with_rematch_arm, _, _}, &1))
  end

  # ---- Multiple-with surface sugar -----------------------------------------

  # `with e1 e2 <arms>` (space-separated scrutinees, comma-separated arm
  # patterns) is SUGAR for nested single-scrutinee `:with_abs`. This test pins
  # the desugared AST shape so it is verified independently of elaboration.
  test "multi-scrutinee `with e1 e2` desugars to nested :with_abs" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(a: Nat, b: Nat) -> Nat =
        with g(a) g(b)
          Z(), Z() -> Z()
          Z(), S(k) -> S(k)
          S(j), Z() -> S(j)
          S(j), S(k) -> S(k)
    """

    assert {:ok, ast} = parse(src)

    # Outermost with_abs: the one whose scrutinee is `g(a)`.
    outer =
      collect(ast, [])
      |> Enum.find(fn
        {:with_abs, _, [{:function_call, m, [{:variable, _, "a"}]} | _]} ->
          Keyword.get(m, :name) == "g"

        _ ->
          false
      end)

    assert {:with_abs, _meta, [outer_scrut | outer_arms]} = outer
    assert {:function_call, gm, [{:variable, _, "a"}]} = outer_scrut
    assert Keyword.get(gm, :name) == "g"

    # Two distinct first patterns Z() and S(j) → two grouped outer arms.
    assert length(outer_arms) == 2

    assert [{:match_arm, m0, [inner0]}, {:match_arm, m1, [inner1]}] = outer_arms
    assert {:function_call, p0m, []} = Keyword.get(m0, :pattern)
    assert Keyword.get(p0m, :name) == "Z"
    assert {:function_call, p1m, [{:variable, _, "j"}]} = Keyword.get(m1, :pattern)
    assert Keyword.get(p1m, :name) == "S"

    # Each outer arm body is an inner with_abs over `g(b)` with two arms.
    for inner <- [inner0, inner1] do
      assert {:with_abs, _, [{:function_call, bm, [{:variable, _, "b"}]} | inner_arms]} = inner
      assert Keyword.get(bm, :name) == "g"
      assert length(inner_arms) == 2
      assert Enum.all?(inner_arms, &match?({:match_arm, _, [_]}, &1))
    end
  end

  # Multiple-with combined with an LHS re-match (`| pat`) is out of scope in the
  # first slice and must be a clean parse error, not a silent mis-parse.
  test "multi-scrutinee with-arm + LHS rematch is rejected" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(a: Nat, b: Nat) -> Nat =
        with g(a) g(b)
          Z(), Z() | Z() -> Z()
    """

    assert {:error, errors} = parse(src)
    assert Enum.any?(errors, &match?({:with_multi_rematch_unsupported, _, _}, &1))
  end

  # Two arms whose first pattern shares a constructor head but differs in
  # sub-structure (`S(j)` vs `S(m)`) would need variable renaming to share an
  # outer branch; the first slice rejects this rather than mis-bind.
  test "multi-scrutinee inconsistent shared-head first patterns are rejected" do
    src = """
    mod M
      type Nat = Z | S(Nat)
      fn foo(a: Nat, b: Nat) -> Nat =
        with g(a) g(b)
          S(j), Z() -> S(j)
          S(m), S(k) -> S(k)
    """

    assert {:error, errors} = parse(src)
    assert Enum.any?(errors, &match?({:with_multi_inconsistent_pattern, _, _}, &1))
  end
end
