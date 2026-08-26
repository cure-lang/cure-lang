defmodule Cure.Elab.TypealiasTest do
  # `typealias NAME = RHS` is a TRANSPARENT type synonym: `NAME` δ-unfolds to
  # `RHS` in conversion, so a `NAME`-typed value is definitionally interchangeable
  # with an `RHS`-typed one. This is distinct from `type NAME = Ctor(...)`, which
  # declares a NOMINAL single-constructor ADT (a wrapper, not a synonym). The
  # motivating use is `typealias Char = Bounded(1114112)` — a numeric index that
  # rides a single compact `nat_lit`, not a 1.1M-node tower.
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  defp parse!(src) do
    {:ok, toks} = Lexer.tokenize(src)
    {:ok, ast} = Parser.parse(toks)
    ast
  end

  describe "parsing" do
    test "typealias produces a transparent :type_annotation node, not an :enum ADT" do
      ast = parse!("mod M\n  typealias Char = Bounded(1114112)\nend\n")
      s = inspect(ast, limit: :infinity)
      assert s =~ ":type_annotation"
      # It must NOT declare a nominal enum named Char with a `Bounded` constructor.
      refute s =~ "container_type: :enum, name: \"Char\""
      # The RHS index is the compact numeric literal, carried as the name node.
      assert s =~ "\"1114112\""
    end

    test "type (not typealias) still declares a single-constructor ADT (unchanged)" do
      ast = parse!("mod M\n  type Wrapper = Wrap(Int)\nend\n")
      s = inspect(ast, limit: :infinity)
      assert s =~ "container_type: :enum, name: \"Wrapper\""
    end
  end

  describe "elaboration: transparency" do
    test "a Char-typed param is definitionally usable at Bounded(1114112)" do
      src = """
      mod M
        use Std.Bounded
        typealias Char = Bounded(1114112)
        fn coerce(c: Char) -> Bounded(1114112) = c
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end
  end
end
