defmodule Cure.Compiler.MacroRawTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, MacroModule, MacroRaw, Parser, Token}
  alias Cure.Diagnostic.Renderer

  test "parser preserves a delimited raw hole" do
    source = """
    macro Datalog
      syntax datalog <rules: raw until dedent> becomes rules
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, [rule]}} = Parser.parse(tokens, emit_events: false)
    assert [{:raw_hole, %{name: "rules", delimiter: "dedent"}}] = rule.segments
  end

  test "raw capture stops at the delimiter and preserves the prefix" do
    tokens = [
      %Token{type: :identifier, value: "a", line: 2, col: 1},
      %Token{type: :dedent, value: nil, line: 3, col: 1},
      %Token{type: :identifier, value: "after", line: 3, col: 1}
    ]

    assert {:ok, captured, rest} = MacroRaw.capture(tokens, "dedent")
    assert Enum.map(captured, & &1.value) == ["a"]
    assert [%Token{value: "after"}] = rest
  end

  test "raw capture reports a missing delimiter" do
    token = %Token{type: :identifier, value: "a", line: 1, col: 1}
    assert {:error, {:missing_raw_delimiter, "dedent"}} = MacroRaw.capture([token], "dedent")
  end

  test "malformed raw capture inputs return verdicts instead of raising" do
    assert {:error, :invalid_raw_tokens} = MacroRaw.capture([42], "dedent")
    assert {:error, :invalid_raw_tokens} = MacroRaw.capture(:tokens, "dedent")
    assert {:error, {:invalid_raw_delimiter, :dedent}} = MacroRaw.capture([], :dedent)
  end

  test "every raw capture failure has stable macro-specific output" do
    cases = [
      {{:missing_raw_delimiter, "dedent"},
       """
       -- RAW MACRO INPUT IS NOT TERMINATED [E092] ------------------------------------

       This raw macro capture reaches the end of its input without the `dedent`
       delimiter.

       Hint: Add the `dedent` delimiter after the raw input
       """},
      {{:invalid_raw_delimiter, :dedent},
       """
       -- RAW MACRO DELIMITER IS INVALID [E092] ---------------------------------------

       A raw macro delimiter must be text, but this capture uses `dedent`.

       Hint: Use a textual token or structural delimiter name
       """},
      {:invalid_raw_tokens,
       """
       -- RAW MACRO TOKEN STREAM IS MALFORMED [E092] ----------------------------------

       Raw macro capture expected a list of lexer tokens.

       Hint: Pass the lexer tokens belonging to the raw macro input
       """}
    ]

    Enum.each(cases, fn {reason, expected} ->
      {diagnostic, registry} = Errors.to_diagnostic(reason, "raw.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_raw_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end

  test "computed macro uses bind raw spans without consuming the enclosing dedent" do
    source = """
    macro Datalog
      syntax datalog <rules: raw until dedent> computed by build
    datalog
      rule one
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:block, _, children}} = Parser.parse(tokens, emit_events: false)

    assert [{:computed_use, _, [_elab, {:macro_input, _, [{:raw_tokens, meta, captured}]}]}] =
             Enum.filter(children, &match?({:computed_use, _, _}, &1))

    assert Keyword.get(meta, :delimiter) == "dedent"
    assert Enum.any?(captured, &(&1.value == "rule"))
  end

  test "generated raw fillers assemble through the reader-tier delimiter" do
    source = "macro Datalog\n  syntax datalog <rules: raw until dedent> becomes rules\n"
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, [rule]}} = Parser.parse(tokens, emit_events: false)
    assert {:ok, use_site} = Cure.Compiler.MacroFuzz.assemble_use_site(rule, %{"rules" => {:raw_text, "item"}})
    assert {:raw_tokens, _, captured} = Parser.expand_example([rule], use_site)
    assert Enum.map(captured, & &1.value) == ["item"]
  end

  test "module rules execute to ordinary AST without loading a module" do
    source = """
    macro Board
      syntax module <decl: Code> becomes decl
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:macro_def, _, rules}} = Parser.parse(tokens, emit_events: false)
    rule = Enum.find(rules, &(&1[:module_rule] == true))

    assert {:ok, {:literal, _meta, 1}} =
             MacroModule.execute_module_rule(rule, rules, %{"decl" => {:int_lit, 1}})

    assert {:error, :not_a_module_rule} =
             MacroModule.execute_module_rule(%{kind: :syntax, module_rule: false}, rules, %{})
  end

  test "open categories compose extensions and reject closed categories" do
    base = [%{kind: :open_category, name: "Clause"}, %{kind: :syntax, keyword: "base", category: "Clause"}]
    extension = [%{kind: :syntax, keyword: "extra", category: "Clause"}]
    assert {:ok, rules} = MacroModule.compose_open_categories(base, extension)
    assert Enum.map(rules, & &1[:keyword]) == [nil, "base", "extra"]

    closed = [%{kind: :syntax, keyword: "other", category: "Other"}]

    assert {:error, {:closed_category_extension, ["Other"]}} =
             MacroModule.compose_open_categories(base, closed)

    duplicate = [%{kind: :syntax, keyword: "base", category: "Clause"}]

    assert {:error, {:ambiguous_macro_extension, ["base"]}} =
             MacroModule.compose_open_categories(base, duplicate)
  end

  test "malformed module-macro host values return verdicts instead of raising" do
    rule = %{kind: :syntax, module_rule: true}

    assert {:error, :invalid_module_rule_set} = MacroModule.execute_module_rule(rule, :rules, %{})
    assert {:error, :invalid_module_rule_set} = MacroModule.execute_module_rule(rule, [42], %{})
    assert {:error, :invalid_module_rule_bindings} = MacroModule.execute_module_rule(rule, [], :bindings)
    assert {:error, :invalid_macro_extension_rules} = MacroModule.compose_open_categories(:base, [])
    assert {:error, :invalid_macro_extension_rule} = MacroModule.compose_open_categories([], [42])
  end

  test "every module-macro validation branch has stable user-facing output" do
    cases = [
      {:module_rule_not_fully_consumed,
       """
       -- MODULE MACRO LEAVES INPUT UNCONSUMED [E092] ---------------------------------

       This module macro expands one declaration but leaves additional authored tokens
       outside the matched rule.

       Hint: Extend the rule to consume the remaining tokens or remove them
       """},
      {:not_a_module_rule,
       """
       -- MACRO RULE CANNOT EXPAND A MODULE [E092] ------------------------------------

       This rule is being executed as a module macro, but it was not declared with
       module scope.

       Hint: Declare this syntax as a module rule before executing it here
       """},
      {:invalid_module_rule_set,
       """
       -- MODULE MACRO RULE SET IS MALFORMED [E092] -----------------------------------

       Module expansion needs a list containing valid syntax rules from the same macro.

       Hint: Provide the parsed syntax rules that own this module rule
       """},
      {:invalid_module_rule_bindings,
       """
       -- MODULE MACRO BINDINGS ARE MALFORMED [E092] ----------------------------------

       Module-rule bindings must map each declared hole name to its captured syntax
       value.

       Hint: Provide a map from hole names to captured syntax
       """},
      {:invalid_macro_extension_rules,
       """
       -- MACRO EXTENSION LISTS ARE MALFORMED [E092] ----------------------------------

       Open-category composition needs separate lists of base rules and extension
       rules.

       Hint: Provide one list of base rules and one list of extension rules
       """},
      {:invalid_macro_extension_rule,
       """
       -- MACRO EXTENSION RULE IS MALFORMED [E092] ------------------------------------

       Every base or extension rule must be a parsed macro-rule map.

       Hint: Provide valid parsed macro rules in both lists
       """},
      {{:closed_category_extension, ["Other"]},
       """
       -- CLOSED MACRO CATEGORY CANNOT BE EXTENDED [E092] -----------------------------

       The extension adds syntax to closed category `Other`, but only categories
       declared open accept external rules.

       Hint: Declare the category open or move the syntax into its owning macro
       """},
      {{:ambiguous_macro_extension, ["item"]},
       """
       -- MACRO EXTENSION REPEATS A KEYWORD [E092] ------------------------------------

       The composed macro would contain multiple rules beginning with keyword `item`,
       making dispatch ambiguous.

       Hint: Give each composed rule a distinct leading keyword
       """}
    ]

    Enum.each(cases, fn {reason, expected} ->
      {diagnostic, registry} = Errors.to_diagnostic(reason, "module_macro.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_module_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end
end
