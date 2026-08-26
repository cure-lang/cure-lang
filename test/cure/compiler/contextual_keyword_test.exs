defmodule Cure.Compiler.ContextualKeywordTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  test "proof is lexed as an identifier" do
    assert {:ok, [token | _]} = Lexer.tokenize("proof", emit_events: false)
    assert token.type == :identifier
    assert token.value == "proof"
    assert :proof in Lexer.contextual_keywords()
  end

  test "proof still introduces a proof container at a declaration-shaped head" do
    source = "proof Laws\n  fn reflexive(x: Int) -> Equivalent(Int, x, x) = reflexive(x)\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, meta, _body}} = Parser.parse(tokens, emit_events: false)
    assert meta[:container_type] == :proof
    assert meta[:name] == "Laws"
  end

  test "proof remains an ordinary parameter and value" do
    source = "fn keep(proof: Int) -> Int = proof\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:function_def, meta, [body]}} = Parser.parse(tokens, emit_events: false)
    assert [{:param, _, "proof"}] = meta[:params]
    assert {:variable, _, "proof"} = body
  end

  test "requires is lexed as an identifier" do
    assert {:ok, [token | _]} = Lexer.tokenize("requires", emit_events: false)
    assert token.type == :identifier
    assert token.value == "requires"
    assert :requires in Lexer.contextual_keywords()
  end

  test "requires remains an ordinary parameter and value" do
    source = "fn keep(requires: Int) -> Int = requires\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:function_def, meta, [body]}} = Parser.parse(tokens, emit_events: false)
    assert [{:param, _, "requires"}] = meta[:params]
    assert {:variable, _, "requires"} = body
  end

  test "precedencegroup is lexed as an identifier" do
    assert {:ok, [token | _]} = Lexer.tokenize("precedencegroup", emit_events: false)
    assert token.type == :identifier
    assert token.value == "precedencegroup"
    assert :precedencegroup in Lexer.contextual_keywords()
  end

  test "precedencegroup introduces a precedencegroup container at a declaration-shaped head" do
    # Use a group name absent from the built-in prelude so this isolates
    # contextual-keyword parsing, not prelude conflict detection (which would
    # reject a redeclaration of `Additive` with a divergent body).
    source = "precedencegroup Custom\n  associativity: left\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:precedencegroup, meta, _body}} = Parser.parse(tokens, emit_events: false)
    assert meta[:name] == :Custom
  end

  test "precedencegroup remains an ordinary parameter and value" do
    source = "fn keep(precedencegroup: Int) -> Int = precedencegroup\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:function_def, meta, [body]}} = Parser.parse(tokens, emit_events: false)
    assert [{:param, _, "precedencegroup"}] = meta[:params]
    assert {:variable, _, "precedencegroup"} = body
  end

  test "infix is lexed as an identifier" do
    assert {:ok, [token | _]} = Lexer.tokenize("infix", emit_events: false)
    assert token.type == :identifier
    assert token.value == "infix"
    assert :infix in Lexer.contextual_keywords()
  end

  test "infix introduces a fixity declaration at a declaration-shaped head" do
    source = "infix + : Additive\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:fixity, meta, _body}} = Parser.parse(tokens, emit_events: false)
    assert meta[:fixity] == :infix
    assert meta[:operator] == "+"
    assert meta[:group] == :Additive
  end

  test "infix remains an ordinary parameter and value" do
    source = "fn keep(infix: Int) -> Int = infix\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:function_def, meta, [body]}} = Parser.parse(tokens, emit_events: false)
    assert [{:param, _, "infix"}] = meta[:params]
    assert {:variable, _, "infix"} = body
  end

  test "prefix is lexed as an identifier" do
    assert {:ok, [token | _]} = Lexer.tokenize("prefix", emit_events: false)
    assert token.type == :identifier
    assert token.value == "prefix"
    assert :prefix in Lexer.contextual_keywords()
  end

  test "prefix introduces a fixity declaration at a declaration-shaped head" do
    # Use an operator absent from the built-in prelude so this isolates
    # contextual-keyword parsing, not prelude conflict detection (the prelude
    # already binds prefix `-` to the `Prefix` group).
    source = "prefix `~~` : Negation\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:fixity, meta, _body}} = Parser.parse(tokens, emit_events: false)
    assert meta[:fixity] == :prefix
    assert meta[:operator] == "~~"
    assert meta[:group] == :Negation
  end

  test "prefix remains an ordinary parameter and value" do
    source = "fn keep(prefix: Int) -> Int = prefix\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:function_def, meta, [body]}} = Parser.parse(tokens, emit_events: false)
    assert [{:param, _, "prefix"}] = meta[:params]
    assert {:variable, _, "prefix"} = body
  end

  test "postfix is lexed as an identifier" do
    assert {:ok, [token | _]} = Lexer.tokenize("postfix", emit_events: false)
    assert token.type == :identifier
    assert token.value == "postfix"
    assert :postfix in Lexer.contextual_keywords()
  end

  test "postfix introduces a fixity declaration at a declaration-shaped head" do
    source = "postfix ! : Factorial\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:fixity, meta, _body}} = Parser.parse(tokens, emit_events: false)
    assert meta[:fixity] == :postfix
    assert meta[:operator] == "!"
    assert meta[:group] == :Factorial
  end

  test "postfix remains an ordinary parameter and value" do
    source = "fn keep(postfix: Int) -> Int = postfix\n"

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:function_def, meta, [body]}} = Parser.parse(tokens, emit_events: false)
    assert [{:param, _, "postfix"}] = meta[:params]
    assert {:variable, _, "postfix"} = body
  end
end
