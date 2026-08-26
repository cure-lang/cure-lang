defmodule Cure.Compiler.MacroParseTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, MacroParse}
  alias Cure.Diagnostic.Renderer

  test "builds a pure grammar declaration" do
    productions = [%{name: :word, body: ["word", :Text]}, %{name: :number, body: ["number", :Number]}]
    assert {:ok, %{kind: :quoted_parse_grammar, productions: ^productions}} = MacroParse.build(:Command, productions)
  end

  test "rejects duplicate and left-recursive productions" do
    duplicate = [%{name: :word, body: ["word"]}, %{name: :word, body: ["other"]}]
    assert {:error, :duplicate_parse_production} = MacroParse.build(:Command, duplicate)

    recursive = [%{name: :expr, body: [:expr, "+", :Number]}]
    assert {:error, {:left_recursive_parse_production, [:expr]}} = MacroParse.build(:Command, recursive)
  end

  test "malformed grammar inputs return verdicts instead of raising" do
    assert {:error, {:invalid_parse_name, 42}} = MacroParse.build(42, [])
    assert {:error, :invalid_parse_productions} = MacroParse.build(:Command, :productions)
    assert {:error, :invalid_parse_production} = MacroParse.build(:Command, [42])
  end

  test "every parser-production validation branch has stable user-facing output" do
    duplicate = [%{name: :word, body: ["word"]}, %{name: :word, body: ["other"]}]
    recursive = [%{name: :expr, body: [:expr, "+", :Number]}]

    cases = [
      {fn -> MacroParse.build(42, []) end,
       """
       -- PARSER GRAMMAR NAME IS INVALID [E092] ---------------------------------------

       A generated parser grammar needs an atom or text name, but this grammar uses
       `42`.

       Hint: Use a stable grammar name such as `Command`
       """},
      {fn -> MacroParse.build(:Command, :productions) end,
       """
       -- PARSER PRODUCTIONS ARE MALFORMED [E092] -------------------------------------

       A parser grammar's productions must be provided as an ordered list.

       Hint: Provide a list of named parser productions
       """},
      {fn -> MacroParse.build(:Command, [42]) end,
       """
       -- PARSER PRODUCTION IS MALFORMED [E092] ---------------------------------------

       Every parser production needs an atom or text name and a non-empty body of token
       or production names.

       Hint: Provide `name` and a non-empty `body` list
       """},
      {fn -> MacroParse.build(:Command, duplicate) end,
       """
       -- PARSER PRODUCTION NAME IS REPEATED [E092] -----------------------------------

       Two productions in this grammar have the same name, so references to that
       production would be ambiguous.

       Hint: Give every production in the grammar a unique name
       """},
      {fn -> MacroParse.build(:Command, recursive) end,
       """
       -- PARSER PRODUCTION IS LEFT-RECURSIVE [E092] ----------------------------------

       `expr` begins by invoking itself, so recursive descent would make no progress
       before recurring.

       Hint: Rewrite the production so it consumes a token before recurring
       """}
    ]

    Enum.each(cases, fn {run, expected} ->
      assert {:error, reason} = run.()
      {diagnostic, registry} = Errors.to_diagnostic(reason, "parse.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_parse_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end
end
