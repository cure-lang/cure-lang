defmodule Cure.Compiler.ParserBindPipeTest do
  @moduledoc """
  Parser coverage for the binder pipe `|x|>` (docs/BIND_PIPE.md).

  The construct introduces **no new lexeme** (§3.1): the lexer's greedy `|>`
  token means `|x|>` arrives as three tokens — `:bar`, `:identifier`, `:pipe` —
  and recognition is a parser-side, adjacency-required lookahead (§3.3, §4.2).
  A lone `|` (list cons, or a syntax error in expression position) is untouched.

  The parser MUST emit the *exact* `do`-block node a `do`/`let`-chain desugars to
  (§7.1): `{:block, [do: true, bind_pipe: true, …], [binds…, final]}`, where each
  `|xᵢ|> eᵢ` contributes one `{:assignment, [do_bind: true, …], [pattern, value]}`
  and the final stage is the block's last expression.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # The function body of the single `fn` in a one-module source.
  defp body!(source) do
    {:container, _, [{:function_def, _meta, [body]}]} = parse!(source)
    body
  end

  describe "single stage" do
    test "`a |x|> f(x)` is the `do`-block node with one bind and a final expr" do
      body = body!("mod M\n  fn g() -> Int = 1 |x|> f(x)\n")

      assert {:block, meta, [assignment, final]} = body
      assert meta[:do] == true
      assert meta[:bind_pipe] == true

      assert {:assignment, ameta, [pattern, rhs]} = assignment
      assert ameta[:let] == true
      assert ameta[:do_bind] == true
      assert ameta[:bind_pipe] == true
      assert {:variable, _, "x"} = pattern
      assert {:literal, _, 1} = rhs

      # The stage VALUE is the block's final expression.
      assert {:function_call, fmeta, [_arg]} = final
      assert fmeta[:name] == "f"
    end
  end

  describe "chained stages" do
    test "`a |x|> f(x) |y|> g(y)` folds into two binds and one final expr" do
      body = body!("mod M\n  fn g() -> Int = 1 |x|> f(x) |y|> h(y)\n")

      assert {:block, meta, [bind1, bind2, final]} = body
      assert meta[:bind_pipe] == true

      # bind1: x <- 1
      assert {:assignment, _, [{:variable, _, "x"}, {:literal, _, 1}]} = bind1
      # bind2: y <- f(x)  (the previous stage's value becomes this stage's rhs)
      assert {:assignment, _, [{:variable, _, "y"}, {:function_call, fm, [_]}]} = bind2
      assert fm[:name] == "f"
      # final: h(y)
      assert {:function_call, hm, [_]} = final
      assert hm[:name] == "h"
    end

    test "the head may itself be a block (a `do` block) — treated as the head" do
      # `left` is a non-bind-pipe block: the whole block becomes the first bind's
      # right-hand side and the stage value becomes the final expression.
      src = """
      mod M
        fn g() -> Int =
          do
            y <- eff()
            y
          |x|> f(x)
      """

      body = body!(src)
      assert {:block, meta, [assignment, final]} = body
      assert meta[:bind_pipe] == true
      assert {:assignment, _, [{:variable, _, "x"}, {:block, _, _}]} = assignment
      assert {:function_call, _, _} = final
    end
  end

  describe "layout" do
    test "a stage may open a continuation line (leading `|x|>`)" do
      src = """
      mod M
        fn g() -> Int =
          1
          |x|> f(x)
          |y|> h(y)
      """

      assert {:block, meta, [_, _, _]} = body!(src)
      assert meta[:bind_pipe] == true
    end
  end

  describe "disambiguation — a lone `|` is untouched" do
    test "list cons `[h | t]` still parses as a cons pattern" do
      src = """
      mod M
        fn g(xs: List(Int)) -> List(Int) =
          match xs
            [] -> []
            [h | t] -> [h | t]
      """

      # No bind-pipe block anywhere in the AST.
      assert {:container, _, [fd]} = parse!(src)
      refute has_bind_pipe?(fd)
    end

    test "a lone `|` in expression position does not open a stage" do
      # `1 | 2` is not a valid expression (no infix `|`); the recogniser demands
      # the full adjacent `:bar :identifier :pipe` shape, so this must not parse
      # as a binder pipe.
      assert {:error, _} =
               (case Lexer.tokenize("mod M\n  fn g() -> Int = 1 | 2\n", emit_events: false) do
                  {:ok, tokens} -> Parser.parse(tokens, emit_events: false)
                  other -> other
                end)
    end
  end

  describe "whitespace strictness (§3.3)" do
    test "whitespace between the tokens is not a binder pipe" do
      # `1 | x |> f(x)` — `|` and `x` are not adjacent, so no stage opens; the
      # stream is not a valid expression.
      result =
        case Lexer.tokenize("mod M\n  fn g() -> Int = 1 | x |> f(x)\n", emit_events: false) do
          {:ok, tokens} -> Parser.parse(tokens, emit_events: false)
          other -> other
        end

      assert {:error, _} = result
    end

    test "a space before `|>` breaks the recogniser" do
      result =
        case Lexer.tokenize("mod M\n  fn g() -> Int = 1 |x |> f(x)\n", emit_events: false) do
          {:ok, tokens} -> Parser.parse(tokens, emit_events: false)
          other -> other
        end

      assert {:error, _} = result
    end
  end

  describe "binder names (§3.2, §5.5)" do
    test "a leading-underscore binder is an ordinary identifier" do
      body = body!("mod M\n  fn g() -> Int = 1 |_x|> f(_x)\n")
      assert {:block, meta, [{:assignment, _, [{:variable, _, "_x"}, _]}, _]} = body
      assert meta[:bind_pipe] == true
    end
  end

  # Recursively search for a bind-pipe block anywhere in the AST.
  defp has_bind_pipe?({:block, meta, _} = node) do
    Keyword.get(meta, :bind_pipe, false) or children_have_bind_pipe?(node)
  end

  defp has_bind_pipe?(node), do: children_have_bind_pipe?(node)

  defp children_have_bind_pipe?({_tag, _meta, children}) when is_list(children),
    do: Enum.any?(children, &has_bind_pipe?/1)

  defp children_have_bind_pipe?(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.any?(&has_bind_pipe?/1)

  defp children_have_bind_pipe?(list) when is_list(list),
    do: Enum.any?(list, &has_bind_pipe?/1)

  defp children_have_bind_pipe?(_), do: false
end
