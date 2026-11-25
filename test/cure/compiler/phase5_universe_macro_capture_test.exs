defmodule Cure.Compiler.Phase5UniverseMacroCaptureTest do
  @moduledoc """
  Frontend reflection boundary checks. These are not macro compilation or kernel
  acceptance tests: raw Core universes must never become parser-syntax captures.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{MacroSyntax, Token}
  alias Cure.Core.UniverseLevel, as: L
  alias Cure.Diagnostic.Span
  alias Cure.MetaAST.{Metadata, SourceInfo}

  test "raw universe structures and exact Core universe nodes are refused directly" do
    for capture <- forbidden() do
      assert_raise ArgumentError, ~r/raw Core universes/, fn -> MacroSyntax.to_syntax(capture) end
    end
  end

  test "semantic metadata scalar and list slots cannot hide raw Core universes" do
    for capture <- forbidden(),
        value <- [capture, [capture], [1, [capture]]],
        tag <- [:variable, :literal] do
      ast = {tag, [payload: value], "surface"}
      assert_raise ArgumentError, ~r/raw Core universes/, fn -> MacroSyntax.to_syntax(ast) end
    end
  end

  test "plain map keys and values are recursively checked without making structs Enumerable" do
    for capture <- forbidden(),
        map <- [%{payload: capture}, %{capture => :payload}, %{payload: [%{nested: capture}]}] do
      assert_raise ArgumentError, ~r/raw Core universes/, fn -> MacroSyntax.to_syntax(map) end
    end
  end

  test "Token values and reflected expansion contexts recursively refuse universe captures" do
    for capture <- forbidden() do
      token = Token.new(:identifier, %{payload: [capture]}, 1, 1)
      assert_raise ArgumentError, ~r/raw Core universes/, fn -> MacroSyntax.to_syntax(token) end
      assert_raise ArgumentError, ~r/raw Core universes/, fn -> MacroSyntax.context_syntax(%{payload: capture}) end
    end
  end

  test "child syntax and semantic AST-valued metadata cannot hide universe nodes" do
    for capture <- forbidden() do
      child = {:block, [], [capture]}
      metadata = {:variable, [annotation: {:literal, [payload: capture], 0}], "x"}
      quoted = {:quoted_syntax, [], [child]}

      for ast <- [child, metadata, quoted] do
        assert_raise ArgumentError, ~r/raw Core universes/, fn -> MacroSyntax.to_syntax(ast) end
      end
    end
  end

  test "Type(level) surface syntax and typed binder metadata retain their frontend representation" do
    level = {:variable, [], "l"}
    surface = {:function_call, [name: "Type"], [level]}
    binder = {:param, [name: "A", type: surface, implicit: true], []}

    for ast <- [surface, binder] do
      assert MacroSyntax.from_syntax(MacroSyntax.to_syntax(ast)) == ast
    end

    assert {:syn_node, :function_call, attrs, [_]} = MacroSyntax.to_syntax(surface)
    assert {:name, {:s_str, "Type"}} in attrs
  end

  test "the frontend two-tuple type-any sentinel is not mistaken for a Core universe" do
    assert MacroSyntax.to_syntax({:type, :any}) == {:syn_raw, :s_opaque}

    assert {:syn_leaf, :literal, [{:payload, :s_opaque}], {:s_int, 7}} =
             MacroSyntax.to_syntax({:literal, [payload: {:type, :any}], 7})
  end

  test "opaque native diagnostic structures and regex retain their existing reflection contract" do
    span = struct(Span, source_id: "phase5.cure", path: "phase5.cure", start_line: 1, start_column: 1)
    info = %SourceInfo{whole: span, name: span}

    for opaque <- [span, info, ~r/phase5/u] do
      assert MacroSyntax.to_syntax(opaque) == {:syn_raw, :s_opaque}
    end

    ast = {:variable, [source_info: info, scope: :local, line: 1, col: 1], "l"}
    roundtrip = ast |> MacroSyntax.to_syntax() |> MacroSyntax.from_syntax()
    assert Metadata.source_info(elem(roundtrip, 1)) == info
    assert Keyword.fetch!(elem(roundtrip, 1), :scope) == :local
    assert Keyword.fetch!(elem(roundtrip, 1), :line) == 1
    assert Keyword.fetch!(elem(roundtrip, 1), :col) == 1

    assert {:syn_leaf, :literal, [{:pattern, :s_opaque}], {:s_int, 7}} =
             MacroSyntax.to_syntax({:literal, [pattern: ~r/phase5/u], 7})
  end

  test "ordinary token reflection remains position-insensitive and content-distinguishing" do
    first = MacroSyntax.to_syntax(Token.new(:identifier, "level", 1, 1))
    moved = MacroSyntax.to_syntax(Token.new(:identifier, "level", 90, 42))
    changed = MacroSyntax.to_syntax(Token.new(:identifier, "other", 1, 1))
    assert first == moved
    refute first == changed
  end

  defp forbidden do
    level = L.closed(37)

    [
      level,
      {:level_nf, 37, []},
      {:level_type},
      {:level_value, level},
      {:type, {:finite, level}},
      {:type, {:finite, {:level_nf, 37, []}}},
      {:type, {:omega, 0}},
      {:type, {:omega, 37}},
      {:type, 0},
      {:type, 37},
      {:type, -1}
    ]
  end
end
