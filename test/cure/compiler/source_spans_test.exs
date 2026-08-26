defmodule Cure.Compiler.SourceSpansTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Diagnostic.Span
  alias Cure.Elab.MacroExpand
  alias Cure.MetaAST.Metadata

  test "parser metadata retains complete authored construct and focused name spans" do
    source = "mod Demo\n  fn answer(x: Int) -> Int = helper(x)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "demo.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "demo.cure", emit_events: false, prelude_macros: false)

    spans = collect_spans(ast)
    assert spans != []
    assert Enum.all?(spans, &match?(%Span{source_id: "demo.cure"}, &1))

    function = find_node(ast, :function_def)
    function_span = function |> elem(1) |> Metadata.source_info() |> Map.fetch!(:whole)
    assert slice(source, function_span) =~ "fn answer"
    assert slice(source, function_span) =~ "helper(x)"
    function_info = Metadata.source_info(elem(function, 1))
    assert slice(source, function_info.name) == "answer"
    assert slice(source, function_info.body) == "helper(x)"

    [{:param, parameter_meta, "x"}] = Keyword.fetch!(elem(function, 1), :params)
    parameter_info = Metadata.source_info(parameter_meta)
    assert slice(source, parameter_info.whole) == "x: Int"
    assert slice(source, parameter_info.name) == "x"

    call = find_node(ast, :function_call)
    call_meta = elem(call, 1)
    call_info = Metadata.source_info(call_meta)
    assert call_info.callee != nil
    assert length(call_info.arguments) == 1
    assert slice(source, call_info.callee) == "helper"
    assert slice(source, call_info.whole) == "helper(x)"
    assert Enum.map(call_info.arguments, &slice(source, &1)) == ["x"]
    assert Enum.all?(elem(call, 2), fn child -> match?({_, meta, _} when is_list(meta), child) end)
  end

  test "annotations stored in declaration metadata retain their authored spans" do
    source = "mod Demo\n  fn answer(x: Int) -> Int = x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "demo.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "demo.cure", emit_events: false, prelude_macros: false)

    {:function_def, meta, _body} = find_node(ast, :function_def)
    function_info = Metadata.source_info(meta)
    {:variable, return_meta, "Int"} = Keyword.fetch!(meta, :return_type)
    [{:param, parameter_meta, "x"}] = Keyword.fetch!(meta, :params)
    {:variable, parameter_type_meta, "Int"} = Keyword.fetch!(parameter_meta, :type)

    assert slice(source, Metadata.source_info(return_meta).whole) == "Int"
    assert slice(source, Metadata.source_info(parameter_type_meta).whole) == "Int"
    assert slice(source, function_info.annotation) == "Int"
    assert slice(source, function_info.body) == "x"
  end

  test "lambda metadata owns its parameters, arrow, body, and complete expression" do
    source = "mod Demo\n  fn use() = apply(fn (left, right) -> left end)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "lambda.cure", emit_events: false)

    assert {:ok, ast} =
             Parser.parse(tokens, file: "lambda.cure", emit_events: false, prelude_macros: false)

    {:lambda, meta, [_body]} = find_node(ast, :lambda)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "fn (left, right) -> left end"
    assert slice(source, info.opener) == "fn"
    assert slice(source, info.closer) == "end"
    assert slice(source, info.operator) == "->"
    assert slice(source, info.body) == "left"
    assert slice(source, info.fields.parameters) == "(left, right)"
    assert slice(source, info.fields.parameter_opener) == "("
    assert slice(source, info.fields.parameter_closer) == ")"
    assert Enum.map(info.arguments, &slice(source, &1)) == ["left", "right"]
  end

  test "parameter source info owns the authored annotation range" do
    source = "fn answer({value: Int}, @linear count : Nat) -> Int = count\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "params.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "params.cure", emit_events: false, prelude_macros: false)

    {:function_def, meta, _body} = find_node(ast, :function_def)
    [{:param, implicit_meta, "value"}, {:param, explicit_meta, "count"}] = Keyword.fetch!(meta, :params)

    assert slice(source, Metadata.source_info(implicit_meta).annotation) == ": Int"
    assert slice(source, Metadata.source_info(explicit_meta).annotation) == ": Nat"
  end

  test "all parameter forms own binder, annotation, initializer, and whole ranges" do
    source =
      "fn configure({token: Int}, to destination: String = \"home\", *items: Int, **options: String) -> Int = 0\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "parameters.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "parameters.cure", emit_events: false, prelude_macros: false)
    {:function_def, meta, _body} = find_node(ast, :function_def)

    [implicit, labelled, variadic, keyword_variadic] = Keyword.fetch!(meta, :params)

    for {{:param, parameter_meta, name}, expected_name, expected_whole, expected_annotation} <- [
          {implicit, "token", "{token: Int}", ": Int"},
          {labelled, "destination", "to destination: String = \"home\"", ": String"},
          {variadic, "items", "*items: Int", ": Int"},
          {keyword_variadic, "options", "**options: String", ": String"}
        ] do
      info = Metadata.source_info(parameter_meta)
      assert name == expected_name
      assert slice(source, info.name) == expected_name
      assert slice(source, info.whole) == expected_whole
      assert slice(source, info.annotation) == expected_annotation
    end

    assert slice(source, labelled |> elem(1) |> Metadata.source_info() |> Map.fetch!(:body)) == "\"home\""

    implicit_info = implicit |> elem(1) |> Metadata.source_info()
    assert slice(source, implicit_info.opener) == "{"
    assert slice(source, implicit_info.closer) == "}"

    labelled_info = labelled |> elem(1) |> Metadata.source_info()
    variadic_info = variadic |> elem(1) |> Metadata.source_info()
    keyword_variadic_info = keyword_variadic |> elem(1) |> Metadata.source_info()

    assert slice(source, Map.fetch!(variadic_info.fields, :variadic_marker)) == "*"
    assert slice(source, Map.fetch!(keyword_variadic_info.fields, :variadic_marker)) == "**"
    assert slice(source, Map.fetch!(labelled_info.fields, :label)) == "to"
    assert slice(source, labelled_info.operator) == "="
  end

  test "let bindings retain their authored whole, name, and annotation ranges" do
    source = "fn answer() -> Int = let value: Int = 1\n  value\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "let.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "let.cure", emit_events: false, prelude_macros: false)

    assignment = find_node(ast, :assignment)
    info = Metadata.source_info(elem(assignment, 1))

    assert slice(source, info.whole) == "let value: Int = 1"
    assert slice(source, info.name) == "value"
    assert slice(source, info.annotation) == ": Int"
  end

  test "macro declarations retain the authored container and macro name ranges" do
    source = "macro Every\n  syntax every becomes Clock.now()\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro.cure", emit_events: false)

    assert {:ok, {:macro_def, meta, [rule]}} =
             Parser.parse(tokens, file: "macro.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == "macro Every\n  syntax every becomes Clock.now()"
    assert slice(source, info.name) == "Every"
    assert slice(source, rule.source_span) == "syntax every becomes Clock.now()"
  end

  test "structured macro sections retain authored entry ranges" do
    source =
      "macro actor <name: ModuleName>\n" <>
        "  syntax family ActorDefinition\n" <>
        "    syntax actor <name: ModuleName>\n" <>
        "    state Type\n" <>
        "  accepts ActorDefinition\n" <>
        "  expands with derive_actor\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro_sections.cure", emit_events: false)

    assert {:ok, {:macro_def, _meta, [family, accepts, expands]}} =
             Parser.parse(tokens, file: "macro_sections.cure", emit_events: false, prelude_macros: false)

    assert slice(source, family.source_span) ==
             "syntax family ActorDefinition\n    syntax actor <name: ModuleName>\n    state Type"

    assert slice(source, accepts.source_span) == "accepts ActorDefinition"
    assert slice(source, expands.source_span) == "expands with derive_actor"
    assert [field] = family.fields
    assert slice(source, field.source_span) == "state Type"
    assert [production] = family.productions
    assert slice(source, production.source_span) == "syntax actor <name: ModuleName>"
  end

  test "macro failure and explanation sections retain authored ranges" do
    source =
      "macro Protocol\n" <>
        "  fail ReplyBeforeRequest(state: Code)\n" <>
        "  explain\n" <>
        "    ReplyBeforeRequest => \"a reply needs an open request\"\n" <>
        "  open Category\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro_diagnosis.cure", emit_events: false)

    assert {:ok, {:macro_def, _meta, [failure, explanation, open]}} =
             Parser.parse(tokens, file: "macro_diagnosis.cure", emit_events: false, prelude_macros: false)

    assert slice(source, failure.source_span) == "fail ReplyBeforeRequest(state: Code)"
    assert slice(source, explanation.source_span) =~ "explain\n    ReplyBeforeRequest"
    [clause] = explanation.clauses
    assert slice(source, clause.source_span) == "ReplyBeforeRequest => \"a reply needs an open request\""
    assert slice(source, open.source_span) == "open Category"
  end

  test "macro examples retain their authored range" do
    source =
      "macro Every\n" <>
        "  syntax every <t: Duration> becomes Timer.repeat(t)\n" <>
        "    example every 500 expands Timer.repeat(500)\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro_example.cure", emit_events: false)

    assert {:ok, {:macro_def, _meta, [rule]}} =
             Parser.parse(tokens, file: "macro_example.cure", emit_events: false, prelude_macros: false)

    [example] = rule.examples
    assert slice(source, example.source_span) == "example every 500 expands Timer.repeat(500)"
  end

  test "named containers retain exact declaration and qualified-name ranges" do
    source = "mod Demo.Core\n  rec Point\n    x: Int\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "containers.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "containers.cure", emit_events: false, prelude_macros: false)

    {:container, module_meta, [record]} = ast
    {:container, record_meta, _fields} = record

    module_info = Metadata.source_info(module_meta)
    record_info = Metadata.source_info(record_meta)
    assert slice(source, module_info.whole) == "mod Demo.Core\n  rec Point\n    x: Int"
    assert slice(source, module_info.opener) == "mod"
    assert slice(source, module_info.name) == "Demo.Core"
    assert Enum.map(module_info.branches, &slice(source, &1)) == ["rec Point\n    x: Int"]
    assert slice(source, record_info.whole) == "rec Point\n    x: Int"
    assert slice(source, record_info.opener) == "rec"
    assert slice(source, record_info.name) == "Point"
    assert Enum.map(record_info.branches, &slice(source, &1)) == ["x: Int"]
  end

  test "parameterized records retain their type-parameter and field declaration ranges" do
    source = "rec Box(T)\n  value: T\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "record.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "record.cure", emit_events: false, prelude_macros: false)

    {:container, meta, _} = find_node(ast, :container)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "rec Box(T)\n  value: T"
    assert slice(source, info.name) == "Box"
    assert slice(source, Map.fetch!(info.fields, :type_parameters)) == "(T)"
    assert Enum.map(info.branches, &slice(source, &1)) == ["value: T"]
  end

  test "proof containers retain exact dotted names and child declaration ranges" do
    source = "proof Laws.Identity\n  fn reflexive(x: Int) -> Int = x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "proof.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "proof.cure", emit_events: false, prelude_macros: false)

    {:container, meta, _} = find_node(ast, :container)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "proof Laws.Identity\n  fn reflexive(x: Int) -> Int = x"
    assert slice(source, info.opener) == "proof"
    assert slice(source, info.name) == "Laws.Identity"
    assert Enum.map(info.branches, &slice(source, &1)) == ["fn reflexive(x: Int) -> Int = x"]
  end

  test "type declarations and aliases retain exact declaration and name ranges" do
    source = "typealias UserId = Int\ntype Color = Red | Blue deriving Show\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "types.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "types.cure", emit_events: false, prelude_macros: false)

    {:block, _, [alias, enum]} = ast
    alias_info = Metadata.source_info(elem(alias, 1))
    enum_info = Metadata.source_info(elem(enum, 1))

    assert slice(source, alias_info.whole) == "typealias UserId = Int"
    assert slice(source, alias_info.opener) == "typealias"
    assert slice(source, alias_info.name) == "UserId"
    assert slice(source, alias_info.annotation) == "Int"
    assert slice(source, Map.fetch!(alias_info.fields, :separator)) == "="
    assert slice(source, enum_info.whole) == "type Color = Red | Blue deriving Show"
    assert slice(source, enum_info.opener) == "type"
    assert slice(source, enum_info.name) == "Color"
    assert slice(source, Map.fetch!(enum_info.fields, :separator)) == "="
    assert slice(source, Map.fetch!(enum_info.fields, :deriving)) == "deriving Show"
    assert Enum.map(enum_info.branches, &slice(source, &1)) == ["Red", "Blue"]
  end

  test "ordinary type aliases and empty ADTs use exact RHS boundaries" do
    source = "type Count = Int\ntype Never = |\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "ordinary_types.cure", emit_events: false)

    assert {:ok, {:block, _, [alias_ast, empty_ast]}} =
             Parser.parse(tokens, file: "ordinary_types.cure", emit_events: false, prelude_macros: false)

    alias_info = alias_ast |> elem(1) |> Metadata.source_info()
    empty_info = empty_ast |> elem(1) |> Metadata.source_info()
    assert slice(source, alias_info.whole) == "type Count = Int"
    assert slice(source, alias_info.annotation) == "Int"
    assert slice(source, empty_info.whole) == "type Never = |"
    assert slice(source, Map.fetch!(empty_info.fields, :leading_separator)) == "|"
    assert empty_info.branches == []
  end

  test "the unit declaration owns its authored unit variant" do
    source = "type Unit = ()\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "unit.cure", emit_events: false)

    assert {:ok, {:container, meta, [{:variable, variant_meta, "unit"}]}} =
             Parser.parse(tokens, file: "unit.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    variant_info = Metadata.source_info(variant_meta)
    assert slice(source, info.whole) == "type Unit = ()"
    assert Enum.map(info.branches, &slice(source, &1)) == ["()"]
    assert slice(source, variant_info.whole) == "()"
  end

  test "multiline parameterized ADTs retain leading bars, variants, and deriving ranges" do
    source =
      "type Result(a, e) =\n" <>
        "  | Ok(a)\n" <>
        "  | Err(e) deriving Show, Eq\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "result.cure", emit_events: false)

    assert {:ok, {:container, meta, [_ok, _err]}} =
             Parser.parse(tokens, file: "result.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)
    assert slice(source, Map.fetch!(info.fields, :type_parameters)) == "(a, e)"
    assert slice(source, Map.fetch!(info.fields, :leading_separator)) == "|"
    assert slice(source, Map.fetch!(info.fields, :deriving)) == "deriving Show, Eq"
    assert Enum.map(info.branches, &slice(source, &1)) == ["Ok(a)", "Err(e)"]
  end

  test "parameterized type aliases retain exact parameter and RHS ranges" do
    source = "typealias Pair(a, b) = Tuple(a, b)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "alias.cure", emit_events: false)

    assert {:ok, {:type_annotation, meta, [_rhs]}} =
             Parser.parse(tokens, file: "alias.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == "typealias Pair(a, b) = Tuple(a, b)"
    assert slice(source, Map.fetch!(info.fields, :type_parameters)) == "(a, b)"
    assert slice(source, info.annotation) == "Tuple(a, b)"
  end

  test "primitive declarations end exactly at their authored names" do
    source = "primitive Word\nfn next(x: Word) -> Word = x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "primitive.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "primitive.cure", emit_events: false, prelude_macros: false)

    {:block, _, [{:container, meta, []}, _function]} = ast
    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == "primitive Word"
    assert slice(source, info.opener) == "primitive"
    assert slice(source, info.name) == "Word"
  end

  test "opaque type declarations own their complete parameterized headers" do
    source = "opaque type Handle(resource: Type)\nfn keep(x: Int) -> Int = x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "opaque.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "opaque.cure", emit_events: false, prelude_macros: false)

    {:block, _, [{:container, meta, []}, _function]} = ast
    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == "type Handle(resource: Type)"
    assert slice(source, info.opener) == "type"
    assert slice(source, info.name) == "Handle"
    assert slice(source, Map.fetch!(info.fields, :type_parameters)) == "(resource: Type)"
  end

  test "indexed families own parameter, index, and constructor signature ranges" do
    source =
      "type Vec(a: Type) indices (n: Nat)\n" <>
        "  Nil: Vec(a, Zero)\n" <>
        "  Cons: a -> Vec(a, n) -> Vec(a, Succ(n))\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "indexed.cure", emit_events: false)

    assert {:ok, {:indexed_type, meta, [nil_ctor, cons_ctor]}} =
             Parser.parse(tokens, file: "indexed.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)
    assert slice(source, info.opener) == "type"
    assert slice(source, info.name) == "Vec"
    assert slice(source, Map.fetch!(info.fields, :type_parameters)) == "(a: Type)"
    assert slice(source, Map.fetch!(info.fields, :indices)) == "indices (n: Nat)"

    assert Enum.map(info.branches, &slice(source, &1)) == [
             "Nil: Vec(a, Zero)",
             "Cons: a -> Vec(a, n) -> Vec(a, Succ(n))"
           ]

    nil_info = nil_ctor |> elem(1) |> Metadata.source_info()
    cons_info = cons_ctor |> elem(1) |> Metadata.source_info()
    assert slice(source, nil_info.name) == "Nil"
    assert slice(source, Map.fetch!(nil_info.fields, :separator)) == ":"
    assert slice(source, nil_info.annotation) == "Vec(a, Zero)"
    assert slice(source, cons_info.annotation) == "a -> Vec(a, n) -> Vec(a, Succ(n))"
  end

  test "indexed constructor ranges include implicit and named dependent domains" do
    source = "type Witness indices (n: Nat)\n  Mk: {k: Nat} -> (value: Nat) -> Witness(k)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "dependent_ctor.cure", emit_events: false)

    assert {:ok, {:indexed_type, meta, [{:gadt_ctor, ctor_meta, _signature}]}} =
             Parser.parse(tokens, file: "dependent_ctor.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    ctor_info = Metadata.source_info(ctor_meta)

    assert Enum.map(info.branches, &slice(source, &1)) == [
             "Mk: {k: Nat} -> (value: Nat) -> Witness(k)"
           ]

    assert slice(source, ctor_info.annotation) == "{k: Nat} -> (value: Nat) -> Witness(k)"
  end

  test "ADT variants retain exact constructor names and extents" do
    source = "type Maybe = None | Some(Int)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "variants.cure", emit_events: false)

    assert {:ok, {:container, _meta, [none, some]}} =
             Parser.parse(tokens, file: "variants.cure", emit_events: false, prelude_macros: false)

    {:variable, none_meta, "None"} = none
    {:function_def, some_meta, []} = some
    none_info = Metadata.source_info(none_meta)
    some_info = Metadata.source_info(some_meta)

    assert slice(source, none_info.name) == "None"
    assert slice(source, none_info.whole) == "None"
    assert slice(source, some_info.name) == "Some"
    assert slice(source, some_info.whole) == "Some(Int)"
  end

  test "imports and fixity declarations retain authored source roles" do
    source = "use Std.List as L\nprecedencegroup additive\ninfix <+> : additive\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "declarations.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "declarations.cure", emit_events: false, prelude_macros: false)

    import = find_node(ast, :import)
    group = find_node(ast, :precedencegroup)
    fixity = find_node(ast, :fixity)
    import_info = Metadata.source_info(elem(import, 1))
    group_info = Metadata.source_info(elem(group, 1))
    fixity_info = Metadata.source_info(elem(fixity, 1))

    assert slice(source, import_info.whole) == "use Std.List as L"
    assert slice(source, import_info.opener) == "use"
    assert slice(source, import_info.name) == "Std.List"
    assert slice(source, Map.fetch!(import_info.fields, :alias_keyword)) == "as"
    assert slice(source, Map.fetch!(import_info.fields, :alias)) == "L"
    assert slice(source, group_info.whole) == "precedencegroup additive"
    assert slice(source, group_info.opener) == "precedencegroup"
    assert slice(source, group_info.name) == "additive"
    assert slice(source, fixity_info.whole) == "infix <+> : additive"
    assert slice(source, fixity_info.opener) == "infix"
    assert slice(source, fixity_info.operator) == "<+>"
    assert slice(source, Map.fetch!(fixity_info.fields, :separator)) == ":"
    assert slice(source, fixity_info.name) == "additive"
  end

  test "precedence groups own each field name, separator, value, and whole range" do
    source =
      "precedencegroup comparison\n" <>
        "  associativity: left\n" <>
        "  higher_than: [addition, relation]\n" <>
        "  lower_than: composition\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "precedence.cure", emit_events: false)

    assert {:ok, {:precedencegroup, meta, []}} =
             Parser.parse(tokens, file: "precedence.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)

    assert Enum.map(info.branches, &slice(source, &1)) == [
             "associativity: left",
             "higher_than: [addition, relation]",
             "lower_than: composition"
           ]

    assert slice(source, Map.fetch!(info.fields, {:assoc, :name})) == "associativity"
    assert slice(source, Map.fetch!(info.fields, {:assoc, :separator})) == ":"
    assert slice(source, Map.fetch!(info.fields, {:assoc, :value})) == "left"
    assert slice(source, Map.fetch!(info.fields, {:higher_than, :value})) == "[addition, relation]"
    assert slice(source, Map.fetch!(info.fields, {:lower_than, :whole})) == "lower_than: composition"
  end

  test "lifted modules own dotted names, behaviour, callbacks, and declarations" do
    source =
      "lift module Cure.Generated.Worker\n" <>
        "  behaviour GenServer\n" <>
        "  callback init(arg: Int) returns Int = arg\n" <>
        "  fn helper(x: Int) -> Int = x\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "lift.cure", emit_events: false)

    assert {:ok, {:lift_module, meta, []}} =
             Parser.parse(tokens, file: "lift.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)
    assert slice(source, info.opener) == "lift"
    assert slice(source, info.name) == "Cure.Generated.Worker"
    assert slice(source, Map.fetch!(info.fields, :behaviour)) == "behaviour GenServer"

    assert Enum.map(info.branches, &slice(source, &1)) == [
             "callback init(arg: Int) returns Int = arg",
             "fn helper(x: Int) -> Int = x"
           ]

    [callback] = Keyword.fetch!(meta, :callbacks)
    callback_info = callback.source_info
    assert slice(source, callback_info.name) == "init"
    assert Enum.map(callback_info.arguments, &slice(source, &1)) == ["arg: Int"]
    assert slice(source, Map.fetch!(callback_info.fields, :returns)) == "returns"
    assert slice(source, callback_info.annotation) == "Int"
    assert slice(source, callback_info.operator) == "="
    assert slice(source, callback_info.body) == "arg"
  end

  test "macro declarations and syntax rules own exact authored ranges" do
    source =
      "macro Wrapper\n" <>
        "  syntax wrap <value: Expression> where Eq(value) becomes value\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "macro.cure", emit_events: false)

    assert {:ok, {:macro_def, meta, [rule]}} =
             Parser.parse(tokens, file: "macro.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)
    assert slice(source, info.opener) == "macro"
    assert slice(source, info.name) == "Wrapper"

    assert Enum.map(info.branches, &slice(source, &1)) == [
             "syntax wrap <value: Expression> where Eq(value) becomes value"
           ]

    assert slice(source, rule.source_span) ==
             "syntax wrap <value: Expression> where Eq(value) becomes value"

    assert [%{source_span: obligation_span}] = rule.obligations
    assert slice(source, obligation_span) == "where Eq(value)"
  end

  test "syntax families own productions, includes, and semantic fields" do
    source =
      "macro Families\n" <>
        "  syntax family Base\n" <>
        "    syntax base <id: Expression>\n" <>
        "  syntax family Child\n" <>
        "    includes Base\n" <>
        "    syntax child <id: Expression>\n" <>
        "    optional label Name where Eq(label)\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "family.cure", emit_events: false)

    assert {:ok, {:macro_def, meta, [_base, family]}} =
             Parser.parse(tokens, file: "family.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)

    assert slice(source, family.source_span) ==
             "syntax family Child\n    includes Base\n    syntax child <id: Expression>\n    optional label Name where Eq(label)"

    assert [production] = family.productions
    assert slice(source, production.source_span) == "syntax child <id: Expression>"
    assert [field] = family.fields
    assert slice(source, field.source_span) == "optional label Name where Eq(label)"
  end

  test "selective imports retain their exact path, selection, alias, and whole ranges" do
    source = "use Std.List.{map, fold} as Lists\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "selective.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "selective.cure", emit_events: false, prelude_macros: false)

    {:import, meta, _} = find_node(ast, :import)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "use Std.List.{map, fold} as Lists"
    assert slice(source, info.name) == "Std.List"
    assert slice(source, Map.fetch!(info.fields, :selection)) == "{map, fold}"
    assert slice(source, Map.fetch!(info.fields, :alias_keyword)) == "as"
    assert slice(source, Map.fetch!(info.fields, :alias)) == "Lists"
  end

  test "protocol and interface declarations retain authored name ranges" do
    source = "proto Show(T)\n  fn show(x: T) -> String\ninterface Eq(T)\n  fn eq(x: T, y: T) -> Bool\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "traits.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "traits.cure", emit_events: false, prelude_macros: false)

    proto = find_node(ast, :container)
    interface = find_node(ast, :interface)
    proto_info = Metadata.source_info(elem(proto, 1))
    interface_info = Metadata.source_info(elem(interface, 1))

    assert slice(source, proto_info.whole) == "proto Show(T)\n  fn show(x: T) -> String"
    assert slice(source, proto_info.opener) == "proto"
    assert slice(source, proto_info.name) == "Show"
    assert slice(source, Map.fetch!(proto_info.fields, :type_parameters)) == "(T)"
    assert Enum.map(proto_info.branches, &slice(source, &1)) == ["fn show(x: T) -> String"]
    assert slice(source, interface_info.whole) == "interface Eq(T)\n  fn eq(x: T, y: T) -> Bool"
    assert slice(source, interface_info.opener) == "interface"
    assert slice(source, interface_info.name) == "Eq"
    assert slice(source, Map.fetch!(interface_info.fields, :type_parameters)) == "(T)"
    assert Enum.map(interface_info.branches, &slice(source, &1)) == ["fn eq(x: T, y: T) -> Bool"]
  end

  test "an empty protocol range ends at its authored header" do
    source = "proto Empty(T)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "empty_proto.cure", emit_events: false)

    assert {:ok, {:container, meta, []}} =
             Parser.parse(tokens, file: "empty_proto.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == "proto Empty(T)"
    assert slice(source, Map.fetch!(info.fields, :type_parameters)) == "(T)"
    assert info.branches == []
  end

  test "an interface requires clause owns its exact range even without methods" do
    source = "interface Ordered(T) requires Eq(T), Show(T)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "required_interface.cure", emit_events: false)

    assert {:ok, {:interface, meta, []}} =
             Parser.parse(tokens, file: "required_interface.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == "interface Ordered(T) requires Eq(T), Show(T)"
    assert slice(source, Map.fetch!(info.fields, :requires)) == "requires Eq(T), Show(T)"
    assert info.branches == []
  end

  test "interface implementations own their header roles, requirements, and members" do
    source =
      "implementation Std.Eq for Option(Int) as IntOption requires Show(Int)\n" <>
        "  fn eq(x: Option(Int), y: Option(Int)) -> Bool = true\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "implementation.cure", emit_events: false)

    assert {:ok, {:implementation, meta, [_member]}} =
             Parser.parse(tokens, file: "implementation.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)
    assert slice(source, info.opener) == "implementation"
    assert slice(source, info.name) == "Std.Eq"
    assert slice(source, info.annotation) == "Option(Int)"
    assert slice(source, Map.fetch!(info.fields, :for_keyword)) == "for"
    assert slice(source, Map.fetch!(info.fields, :for_type)) == "Option(Int)"
    assert slice(source, Map.fetch!(info.fields, :as_keyword)) == "as"
    assert slice(source, Map.fetch!(info.fields, :as_name)) == "IntOption"
    assert slice(source, Map.fetch!(info.fields, :requirements)) == "requires Show(Int)"

    assert Enum.map(info.branches, &slice(source, &1)) == [
             "fn eq(x: Option(Int), y: Option(Int)) -> Bool = true"
           ]
  end

  test "an empty implementation range ends at its implemented type" do
    source = "implementation Eq for Int\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "empty_implementation.cure", emit_events: false)

    assert {:ok, {:implementation, meta, []}} =
             Parser.parse(tokens, file: "empty_implementation.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == "implementation Eq for Int"
    assert slice(source, info.annotation) == "Int"
    assert info.branches == []
  end

  test "protocol implementations own dotted heads, requirements, and member ranges" do
    source = "impl Std.Show for Option(Int) requires Eq(Int)\n  fn show(x: Option(Int)) -> String = \"x\"\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "protocol_impl.cure", emit_events: false)

    assert {:ok, {:container, meta, [_member]}} =
             Parser.parse(tokens, file: "protocol_impl.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)
    assert slice(source, info.opener) == "impl"
    assert slice(source, info.name) == "Std.Show"
    assert slice(source, info.annotation) == "Option(Int)"
    assert slice(source, Map.fetch!(info.fields, :for_keyword)) == "for"
    assert slice(source, Map.fetch!(info.fields, :requirements)) == "requires Eq(Int)"
    assert Enum.map(info.branches, &slice(source, &1)) == ["fn show(x: Option(Int)) -> String = \"x\""]
  end

  test "an empty protocol implementation range ends at its implemented type" do
    source = "impl Show for Int\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "empty_protocol_impl.cure", emit_events: false)

    assert {:ok, {:container, meta, []}} =
             Parser.parse(tokens, file: "empty_protocol_impl.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == "impl Show for Int"
    assert slice(source, info.annotation) == "Int"
    assert info.branches == []
  end

  test "record declaration fields retain authored parameter ranges" do
    source = "rec Point\n  x: Int = 0\n  y: String\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "record_decl.cure", emit_events: false)

    assert {:ok, {:container, _meta, fields}} =
             Parser.parse(tokens, file: "record_decl.cure", emit_events: false, prelude_macros: false)

    [{:param, x_meta, "x"}, {:param, y_meta, "y"}] = fields
    assert slice(source, Metadata.source_info(x_meta).whole) == "x: Int = 0"
    assert slice(source, Metadata.source_info(x_meta).name) == "x"
    assert slice(source, Metadata.source_info(x_meta).annotation) == ": Int"
    assert slice(source, Metadata.source_info(y_meta).whole) == "y: String"
  end

  test "type applications in annotations retain their closing delimiter" do
    source = "mod Demo\n  fn answer(x: Option(Int)) -> Option(Int) = x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "demo.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "demo.cure", emit_events: false, prelude_macros: false)

    {:function_def, meta, _body} = find_node(ast, :function_def)
    {:function_call, return_meta, _} = Keyword.fetch!(meta, :return_type)
    [{:param, parameter_meta, "x"}] = Keyword.fetch!(meta, :params)
    {:function_call, parameter_type_meta, _} = Keyword.fetch!(parameter_meta, :type)

    assert slice(source, Metadata.source_info(return_meta).whole) == "Option(Int)"
    assert slice(source, Metadata.source_info(parameter_type_meta).whole) == "Option(Int)"
  end

  test "match arms retain parser-owned pattern, guard, body, and whole spans" do
    source = "fn choose(x: Int) -> Int = match x\n  n when n > 0 -> n\n  _ -> 0\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "match.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "match.cure", emit_events: false, prelude_macros: false)

    {:match_arm, arm_meta, _} = find_node(ast, :match_arm)
    info = Metadata.source_info(arm_meta)

    assert slice(source, info.whole) == "n when n > 0 -> n"
    assert slice(source, info.pattern) == "n"
    assert slice(source, info.guard) == "n > 0"
    assert slice(source, info.operator) == "->"
    assert slice(source, info.body) == "n"
  end

  test "impossible match arms retain the authored marker as their exact body" do
    source = "fn absurd(value: Void) -> Int = match value\n  impossible_case -> impossible\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "impossible.cure", emit_events: false)

    assert {:ok, ast} =
             Parser.parse(tokens, file: "impossible.cure", emit_events: false, prelude_macros: false)

    {:match_arm, arm_meta, [nil]} = find_node(ast, :match_arm)
    info = Metadata.source_info(arm_meta)

    assert slice(source, info.whole) == "impossible_case -> impossible"
    assert slice(source, info.operator) == "->"
    assert slice(source, info.body) == "impossible"
  end

  test "pickup expressions and clauses retain exact branch and arrow ranges" do
    source = "fn choose(flag: Bool) -> Int = pickup\n  flag -> 1\n  else -> 0\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "pickup.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "pickup.cure", emit_events: false, prelude_macros: false)

    {:pickup, pickup_meta, [clause, fallback]} = find_node(ast, :pickup)
    pickup_info = Metadata.source_info(pickup_meta)
    assert slice(source, pickup_info.whole) == "pickup\n  flag -> 1\n  else -> 0"
    assert slice(source, pickup_info.opener) == "pickup"
    assert Enum.map(pickup_info.branches, &slice(source, &1)) == ["flag -> 1", "else -> 0"]

    {:pickup_clause, clause_meta, _} = clause
    clause_info = Metadata.source_info(clause_meta)
    assert slice(source, clause_info.condition) == "flag"
    assert slice(source, clause_info.operator) == "->"
    assert slice(source, clause_info.body) == "1"

    {:pickup_else, fallback_meta, _} = fallback
    fallback_info = Metadata.source_info(fallback_meta)
    assert slice(source, fallback_info.name) == "else"
    assert slice(source, fallback_info.operator) == "->"
    assert slice(source, fallback_info.body) == "0"
  end

  test "multi-clause functions retain exact clause roles through parser ownership" do
    source = "fn sign(value: Int) -> Int\n  | 0 -> 0\n  | n when n > 0 -> 1\n  | _ -> -1\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "clauses.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "clauses.cure", emit_events: false, prelude_macros: false)

    {:function_def, function_meta, []} = find_node(ast, :function_def)
    function_info = Metadata.source_info(function_meta)

    assert Enum.map(function_info.branches, &slice(source, &1)) == [
             "| 0 -> 0",
             "| n when n > 0 -> 1",
             "| _ -> -1"
           ]

    [_, guarded, _] = Keyword.fetch!(function_meta, :clauses)
    info = guarded.source_info
    assert slice(source, info.whole) == "| n when n > 0 -> 1"
    assert slice(source, info.opener) == "|"
    assert Enum.map(info.arguments, &slice(source, &1)) == ["n"]
    assert slice(source, info.pattern) == "n"
    assert slice(source, info.guard) == "n > 0"
    assert slice(source, info.operator) == "->"
    assert slice(source, info.body) == "1"
    assert slice(source, function_info.whole) == String.trim_trailing(source)
  end

  test "function signatures own parameters, return, effects, guard, and requirements" do
    source = "fn convert(value: T) -> U ! Io, State when ready requires Show(T), Eq(U)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "signature.cure", emit_events: false)

    assert {:ok, {:function_def, meta, []}} =
             Parser.parse(tokens, file: "signature.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)
    assert slice(source, info.opener) == "fn"
    assert slice(source, info.name) == "convert"
    assert slice(source, Map.fetch!(info.fields, :parameters)) == "(value: T)"
    assert slice(source, Map.fetch!(info.fields, :return_arrow)) == "->"
    assert slice(source, info.annotation) == "U"
    assert slice(source, Map.fetch!(info.fields, :effects)) == "! Io, State"
    assert slice(source, Map.fetch!(info.fields, :guard)) == "when ready"
    assert slice(source, info.guard) == "ready"
    assert slice(source, Map.fetch!(info.fields, :requirements)) == "requires Show(T), Eq(U)"
  end

  test "local functions distinguish the visibility and function keywords" do
    source = "local fn helper(x: Int) -> Int = x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "local_function.cure", emit_events: false)

    assert {:ok, {:function_def, meta, [_body]}} =
             Parser.parse(tokens, file: "local_function.cure", emit_events: false, prelude_macros: false)

    info = Metadata.source_info(meta)
    assert slice(source, info.whole) == String.trim_trailing(source)
    assert slice(source, info.opener) == "local"
    assert slice(source, Map.fetch!(info.fields, :function_keyword)) == "fn"
    assert slice(source, info.name) == "helper"
  end

  test "local bindings retain exact keyword, pattern, annotation, assignment, and value ranges" do
    source = "fn run(value: Int) -> Int =\n  let next: Int = value + 1\n  next\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "binding.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "binding.cure", emit_events: false, prelude_macros: false)

    {:assignment, meta, _} = find_node(ast, :assignment)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "let next: Int = value + 1"
    assert slice(source, info.opener) == "let"
    assert slice(source, info.pattern) == "next"
    assert slice(source, info.name) == "next"
    assert slice(source, info.annotation) == ": Int"
    assert slice(source, info.operator) == "="
    assert slice(source, info.body) == "value + 1"
  end

  test "declaration-local where values retain exact name, assignment, body, and whole ranges" do
    source = "fn run() -> Int = answer\nwhere\n  answer = 42\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "where.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "where.cure", emit_events: false, prelude_macros: false)

    {:function_def, function_meta, _} = find_node(ast, :function_def)
    assert [{:where_value, where_meta, _}] = Keyword.fetch!(function_meta, :where)
    function_info = Metadata.source_info(function_meta)
    info = Metadata.source_info(where_meta)

    assert slice(source, function_info.whole) == String.trim_trailing(source)
    assert slice(source, function_info.operator) == "="
    assert slice(source, Map.fetch!(function_info.fields, :where)) == "where\n  answer = 42"
    assert slice(source, info.whole) == "answer = 42"
    assert slice(source, info.name) == "answer"
    assert slice(source, info.operator) == "="
    assert slice(source, info.body) == "42"
  end

  test "match expressions retain their whole and branch-owned spans" do
    source = "fn choose(x: Int) -> Int = match x\n  n -> n\n  _ -> 0\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "match.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "match.cure", emit_events: false, prelude_macros: false)

    {:pattern_match, meta, _} = find_node(ast, :pattern_match)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "match x\n  n -> n\n  _ -> 0"
    assert slice(source, info.opener) == "match"
    assert Enum.map(info.operands, &slice(source, &1)) == ["x"]
    assert Enum.map(info.branches, &slice(source, &1)) == ["n -> n", "_ -> 0"]
  end

  test "conditionals retain condition and branch-owned spans" do
    source = "fn choose(x: Int) -> Int = if x > 0 then x else 0\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "conditional.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "conditional.cure", emit_events: false, prelude_macros: false)

    {:conditional, meta, _} = find_node(ast, :conditional)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "if x > 0 then x else 0"
    assert slice(source, info.opener) == "if"
    assert slice(source, info.condition) == "x > 0"
    assert slice(source, Map.fetch!(info.fields, :then_keyword)) == "then"
    assert slice(source, info.then_branch) == "x"
    assert slice(source, Map.fetch!(info.fields, :else_keyword)) == "else"
    assert slice(source, info.else_branch) == "0"
  end

  test "single-scrutinee with expressions retain whole and branch spans" do
    source = "fn choose(x: Int) -> Int = with x\n  n -> n\n  _ -> 0\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "with.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "with.cure", emit_events: false, prelude_macros: false)

    {:with_abs, meta, _} = find_node(ast, :with_abs)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "with x\n  n -> n\n  _ -> 0"
    assert Enum.map(info.branches, &slice(source, &1)) == ["n -> n", "_ -> 0"]
  end

  test "multi-scrutinee with preserves the outer authored range" do
    source = "fn choose(a: Int, b: Int) -> Int = with a b\n  x, y -> x\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "with_multi.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "with_multi.cure", emit_events: false, prelude_macros: false)

    {:with_abs, meta, _} = find_node(ast, :with_abs)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "with a b\n  x, y -> x"
    assert Enum.map(info.branches, &slice(source, &1)) == ["x"]
  end

  test "record constructions retain authored name, delimiters, and field spans" do
    source = "fn origin() -> Point = Point{x: 0, y: 0}\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "record.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "record.cure", emit_events: false, prelude_macros: false)

    {:function_call, meta, fields} = find_node(ast, :function_call)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "Point{x: 0, y: 0}"
    assert slice(source, info.name) == "Point"
    assert slice(source, info.opener) == "{"
    assert slice(source, info.closer) == "}"
    assert slice(source, Map.fetch!(info.fields, :x)) == "x"
    assert slice(source, Map.fetch!(info.fields, :y)) == "y"

    assert [x_pair, y_pair] = fields

    for {pair, expected_name, expected_value} <- [{x_pair, "x", "0"}, {y_pair, "y", "0"}] do
      {:pair, pair_meta, _} = pair
      pair_info = Metadata.source_info(pair_meta)
      assert slice(source, pair_info.whole) == "#{expected_name}: #{expected_value}"
      assert slice(source, pair_info.name) == expected_name
      assert slice(source, pair_info.operator) == ":"
      assert slice(source, pair_info.body) == expected_value
    end
  end

  test "explicit map entries and field puns retain exact source roles" do
    source = "fn fields(x: Int) = %{:answer => 42, x}\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "map.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "map.cure", emit_events: false, prelude_macros: false)

    pairs = collect_nodes(ast, :pair)
    assert [explicit, pun] = pairs

    {:pair, explicit_meta, _} = explicit
    explicit_info = Metadata.source_info(explicit_meta)
    assert slice(source, explicit_info.whole) == ":answer => 42"
    assert slice(source, explicit_info.name) == ":answer"
    assert slice(source, explicit_info.operator) == "=>"
    assert slice(source, explicit_info.body) == "42"

    {:pair, pun_meta, _} = pun
    pun_info = Metadata.source_info(pun_meta)
    assert slice(source, pun_info.whole) == "x"
    assert slice(source, pun_info.name) == "x"
    assert pun_info.operator == nil
    assert slice(source, pun_info.body) == "x"
  end

  test "binary segments retain exact values, specifier separators, and terminal ranges" do
    source = "fn encode(value: Int, width: Int) = <<value::integer-signed-size(width), 0>>\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "binary.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "binary.cure", emit_events: false, prelude_macros: false)

    [specified, plain] = collect_nodes(ast, :bin_segment)

    {:bin_segment, specified_meta, _} = specified
    specified_info = Metadata.source_info(specified_meta)
    assert slice(source, specified_info.whole) == "value::integer-signed-size(width)"
    assert slice(source, specified_info.operator) == "::"
    assert slice(source, specified_info.body) == "value"
    assert Enum.map(specified_info.arguments, &slice(source, &1)) == ["width"]

    {:bin_segment, plain_meta, _} = plain
    plain_info = Metadata.source_info(plain_meta)
    assert slice(source, plain_info.whole) == "0"
    assert plain_info.operator == nil
    assert slice(source, plain_info.body) == "0"
  end

  test "operators and containers retain token-owned focused ranges" do
    source =
      "mod Demo\n  fn answer() -> Int = 1 + 2\n  fn xs() -> List(Int) = [1, 2]\n  fn pair() -> Tuple(Int, Int) = %[1, 2]\n" <>
        "  fn fields() = %{x: 1}\n"

    assert {:ok, tokens} = Lexer.tokenize(source, file: "demo.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "demo.cure", emit_events: false, prelude_macros: false)

    binary = find_node(ast, :binary_op)
    binary_info = Metadata.source_info(elem(binary, 1))
    assert slice(source, binary_info.operator) == "+"
    assert Enum.map(binary_info.operands, &slice(source, &1)) == ["1", "2"]

    for {tag, expected} <- [
          {:list, "[1, 2]"},
          {:tuple, "%[1, 2]"},
          {:map, "%{x: 1}"}
        ] do
      node = find_node(ast, tag)
      info = Metadata.source_info(elem(node, 1))
      assert slice(source, info.whole) == expected

      expected_opener =
        case tag do
          :tuple -> "%["
          :map -> "%{"
          :list -> "["
        end

      assert slice(source, info.opener) == expected_opener
      assert slice(source, info.closer) == String.last(expected)
    end
  end

  test "pipe desugaring retains the complete call and aligned argument roles" do
    source = "fn run(value: Int) -> Int = value |> transform(extra: 1)\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "pipe.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "pipe.cure", emit_events: false, prelude_macros: false)

    {:function_call, meta, _arguments} = find_node(ast, :function_call)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "value |> transform(extra: 1)"
    assert slice(source, info.callee) == "transform"
    assert slice(source, info.operator) == "|>"
    assert Enum.map(info.arguments, &slice(source, &1)) == ["value", "1"]
    assert [nil, label] = info.argument_labels
    assert slice(source, label) == "extra"
  end

  test "range expressions retain their exact operator and operand ranges" do
    source = "fn values() = 1..=10\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "range.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "range.cure", emit_events: false, prelude_macros: false)

    {:range, meta, _operands} = find_node(ast, :range)
    info = Metadata.source_info(meta)

    assert slice(source, info.whole) == "1..=10"
    assert slice(source, info.operator) == "..="
    assert Enum.map(info.operands, &slice(source, &1)) == ["1", "10"]
  end

  test "keyword-unary expressions own the keyword through their operand" do
    for {keyword, tag} <- [{"return", :early_return}, {"throw", :throw}, {"yield", :yield}, {"spawn", :async_operation}] do
      source = "fn value() -> Int = #{keyword} 1\n"
      assert {:ok, tokens} = Lexer.tokenize(source, file: "#{keyword}.cure", emit_events: false)

      assert {:ok, ast} =
               Parser.parse(tokens, file: "#{keyword}.cure", emit_events: false, prelude_macros: false)

      {^tag, meta, [_operand]} = find_node(ast, tag)
      info = Metadata.source_info(meta)

      assert slice(source, info.whole) == "#{keyword} 1"
      assert slice(source, info.name) == keyword
      assert slice(source, info.body) == "1"
    end
  end

  test "string interpolation retains its whole and embedded expression ranges" do
    source = ~S|fn message(name: String) -> String = "hello #{name}! #{name + 1}"| <> "\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "interpolation.cure", emit_events: false)

    assert {:ok, ast} =
             Parser.parse(tokens, file: "interpolation.cure", emit_events: false, prelude_macros: false)

    interpolation = find_node(ast, :string_interpolation)
    info = Metadata.source_info(elem(interpolation, 1))

    assert slice(source, info.whole) == ~S|"hello #{name}! #{name + 1}"|
    assert Enum.map(info.arguments, &slice(source, &1)) == ["name", "name + 1"]
  end

  test "attached decorators retain their own name and argument ranges" do
    source = "mod Demo\n  @extern(:erlang, :hd, 2)\n  fn head({T: Type}, xs: List(T)) -> T\n"
    assert {:ok, tokens} = Lexer.tokenize(source, file: "decorator.cure", emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: "decorator.cure", emit_events: false, prelude_macros: false)

    function = find_node(ast, :function_def)
    info = function |> elem(1) |> Metadata.source_info()
    extern = Map.fetch!(info.decorators, "extern")

    assert slice(source, extern.whole) == "@extern(:erlang, :hd, 2)"
    assert slice(source, extern.name) == "extern"
    assert Enum.map(extern.arguments, &slice(source, &1)) == [":erlang", ":hd", "2"]
  end

  test "diagnostic metadata is excluded from semantic comparisons" do
    span = %Span{
      source_id: :one,
      path: "one.cure",
      start_byte: 0,
      end_byte: 1,
      start_line: 1,
      start_column: 1,
      end_line: 1,
      end_column: 2
    }

    plain = {:variable, [line: 1, col: 1, scope: :local], "x"}
    located = {:variable, [line: 1, col: 1, scope: :local, span: span, construct_span: span], "x"}

    assert Metadata.strip_diagnostics(plain) == Metadata.strip_diagnostics(located)
    refute MacroExpand.contains_computed_use?(located)
  end

  defp collect_spans({_, meta, payload}) when is_list(meta) do
    own =
      case Metadata.source_info(meta) do
        %{whole: %Span{} = span} -> [span]
        _ -> []
      end

    own ++ collect_spans(payload)
  end

  defp collect_spans(list) when is_list(list), do: Enum.flat_map(list, &collect_spans/1)
  defp collect_spans(tuple) when is_tuple(tuple), do: tuple |> Tuple.to_list() |> Enum.flat_map(&collect_spans/1)
  defp collect_spans(_), do: []

  defp find_node({node_tag, _, _} = node, wanted_tag) when node_tag == wanted_tag, do: node

  defp find_node({_, _, payload}, tag), do: find_node(payload, tag)

  defp find_node(list, tag) when is_list(list) do
    Enum.find_value(list, &find_node(&1, tag))
  end

  defp find_node(tuple, tag) when is_tuple(tuple), do: tuple |> Tuple.to_list() |> find_node(tag)
  defp find_node(_, _), do: nil

  defp collect_nodes({node_tag, _, payload} = node, wanted_tag) do
    own = if node_tag == wanted_tag, do: [node], else: []
    own ++ collect_nodes(payload, wanted_tag)
  end

  defp collect_nodes(list, tag) when is_list(list), do: Enum.flat_map(list, &collect_nodes(&1, tag))
  defp collect_nodes(tuple, tag) when is_tuple(tuple), do: tuple |> Tuple.to_list() |> collect_nodes(tag)
  defp collect_nodes(_, _), do: []

  defp slice(source, span), do: binary_part(source, span.start_byte, span.end_byte - span.start_byte)
end
