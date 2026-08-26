defmodule Cure.Elab.CharLiteralTest do
  # A character literal is sugar for a compact Bounded literal at the full
  # Unicode bound: `'a'` is `{:bounded_lit, 97}` typed at `Char`. One integer at
  # every stage — never a `Next(...First)` tower. (Char literal PATTERNS, string
  # literals, Binary, Std.String are separate wave items.)
  #
  # These fixtures say `use Std.Char` rather than aliasing the name to
  # `Bounded(0x110000)`. `Char` is `@builtin(:char) opaque type Char` — a nominal
  # carrier, not an alias for its representation — and it is what carries the
  # `ExpressibleByCharacterLiteral` implementation that makes `'a'` mean anything.
  # A local `typealias Char = Bounded(1114112)` shadows that away and asks for a
  # character literal at a type which has no character-literal instance, so what
  # it tested was the alias, not the char literal. The compact representation
  # asserted below is unchanged: the real `Char` lowers `'a'` to `{:bounded_lit, 97}`.
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Elaborator}
  alias Cure.Core.{Env, Context}

  defp body_of(env, name), do: Env.get_def(env, name).body

  # An AST char-literal node (the lexer cannot emit an out-of-range or, until
  # Task 2, a non-ASCII one, so drive those directly through the elaborator).
  defp char_node(cp), do: {:literal, [subtype: :char, line: 1, col: 1], cp}

  describe "elaboration: character literal -> compact bounded_lit" do
    test "an ASCII char literal in infer position is {:bounded_lit, cp}" do
      src = """
      mod M
        use Std.Char
        fn a() -> Char = 'a'
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:bounded_lit, 97} = body_of(env, :a)
    end

    test "a full-plane emoji codepoint stays ONE compact node" do
      src = """
      mod M
        use Std.Char
        fn emoji() -> Char = '😀'
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert {:bounded_lit, 128_512} = body_of(env, :emoji)
    end

    test "end-to-end: a char literal compiles and runs as its codepoint integer" do
      src = """
      mod CharRun
        use Std.Char
        fn emoji() -> Char = '😀'
      end
      """

      {:ok, env} = Program.elaborate(src)

      {:ok, mod} =
        Cure.Elab.Emit.compile_and_load(env, module: :"Cure.CharRun", functions: [:emoji])

      assert apply(mod, :emoji, []) == 128_512
    end

    test "a char literal passed as a plain call argument elaborates (locus 3)" do
      src = """
      mod M
        use Std.Char
        fn plain(c: Char) -> Char = c
        fn a() -> Char = plain('a')
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "a char literal remains Char when used in a dependent index" do
      src = """
      mod CharIndex
        use Std.Char

        type Witness indices (char: Char)
          WitnessA : Witness('a')

        fn witness() -> Witness('a') = WitnessA()
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "an out-of-range codepoint is rejected cleanly (both loci, no crash)" do
      {:ok, sig} = Program.elaborate("mod M\n  use Std.Bounded\nend\n")
      ctx = Context.empty(sig)

      # locus 1 (infer)
      assert {:error, {:char_literal_out_of_range, 0x110000}} =
               Elaborator.elaborate_expr_typed(char_node(0x110000), [], ctx, sig)

      assert {:error, {:char_literal_out_of_range, -1}} =
               Elaborator.elaborate_expr_typed(char_node(-1), [], ctx, sig)

      # locus 3 (scope-only) — the case that would otherwise crash the kernel
      assert {:error, {:char_literal_out_of_range, 0x110000}} =
               Elaborator.elaborate_expr(char_node(0x110000), [], sig)

      assert {:error, {:char_literal_out_of_range, -1}} =
               Elaborator.elaborate_expr(char_node(-1), [], sig)
    end

    test "a char literal with no Bounded family registered errors cleanly, not a crash" do
      # A genuinely bare Env (no `use Std.Bounded` processed) — unlike every
      # other test above, which registers Bounded via `Program.elaborate` on
      # source containing `use Std.Bounded`. `Env.empty()` has `builtins: %{}`,
      # so `char_type_value/1`'s `:no_bounded` branch is reached for real.
      env = Env.empty()
      ctx = Context.empty(env)

      assert {:error, {:char_literal_needs_bounded, 97}} =
               Elaborator.elaborate_expr_typed(char_node(97), [], ctx, env)
    end
  end
end
