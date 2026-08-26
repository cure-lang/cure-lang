defmodule Cure.Compiler.TypeclassParseTest do
  # interface/implementation/deriving are the compile-time typeclass surface
  # (replacing runtime proto/impl). This pins the AST the elaborator consumes.
  use ExUnit.Case, async: true
  alias Cure.Compiler.{Lexer, Parser}

  # `Parser.parse/2` takes a TOKEN LIST, not raw source (@spec parse([Token.t()],
  # keyword())) — mirror the tokenize-then-parse convention every other parser
  # test uses. The parsed AST is a plain `{atom(), keyword(), term()}` tuple, not
  # a struct, so there is no `.definitions` field — a `mod ... end` block parses
  # to `{:container, [container_type: :module, ...], body}`; `body` is the
  # definitions list.
  defp defs(src) do
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)

    # `mod ... end` closes the module by dedent, so a trailing `end` keyword
    # lands as a stray top-level token and the whole file wraps in a `:block`.
    # Dig out the module container's body regardless of that wrapping.
    items =
      case ast do
        {:block, _m, xs} -> xs
        other -> [other]
      end

    {:container, _meta, body} =
      Enum.find(items, fn
        {:container, meta, _} -> Keyword.get(meta, :container_type) == :module
        _ -> false
      end)

    body
  end

  test "an interface with a method and a default method parses" do
    src = """
    mod M
      interface Equatable(a)
        fn eq(x: a, y: a) -> Bool
        fn ne(x: a, y: a) -> Bool = true
    end
    """

    assert Enum.any?(defs(src), &match?({:interface, _, _}, &1))
    {:interface, meta, methods} = Enum.find(defs(src), &match?({:interface, _, _}, &1))
    assert Keyword.get(meta, :name) == "Equatable"
    assert Keyword.get(meta, :params) == ["a"]
    assert length(methods) >= 1
    assert Map.has_key?(Keyword.get(meta, :defaults, %{}), "ne")
  end

  test "an anonymous implementation parses with interface + for-type" do
    src = """
    mod M
      implementation Equatable for Int
        fn eq(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """

    {:implementation, meta, _methods} = Enum.find(defs(src), &match?({:implementation, _, _}, &1))
    assert Keyword.get(meta, :interface) == "Equatable"
    assert Keyword.get(meta, :as) == nil
  end

  test "a named implementation records its name" do
    src = """
    mod M
      implementation Equatable for Int as strictInt
        fn eq(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """

    {:implementation, meta, _} = Enum.find(defs(src), &match?({:implementation, _, _}, &1))
    assert Keyword.get(meta, :as) == "strictInt"
  end

  test "decl-attached deriving is recorded on the type" do
    src = """
    mod M
      type Color = R | G | B deriving Equatable
    end
    """

    # An ADT type def parses to `{:container, meta, variants}` with
    # `meta[:container_type] == :enum` and a STRING `:name`. Matching on a
    # `:type` node would never find anything.
    type_def =
      Enum.find(defs(src), fn
        {:container, meta, _} ->
          Keyword.get(meta, :container_type) == :enum and Keyword.get(meta, :name) == "Color"

        _ ->
          false
      end)

    {:container, meta, _} = type_def
    assert "Equatable" in Keyword.get(meta, :deriving, [])
  end
end
