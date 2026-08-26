defmodule Cure.Elab.BinarySyntaxTest do
  @moduledoc """
  Byte-granular binary syntax in the dependent pipeline: construction
  `<<b1, b2, …>>` and patterns `<<b, rest::binary>>`. The classic codegen lowered
  these to Erlang bit-syntax; here they desugar (in the elaborator, before Core)
  to `Std.Binary` byte primitives — `of_bytes` for construction, and
  `byte_at`/`drop_bytes` guarded by `byte_size` for patterns — over the `Binary`
  primitive type. Nothing new reaches the kernel and there is no Core binary
  former.

  Scope: default 8-bit-integer segments plus a trailing `rest::binary`. Sized or
  typed bit segments (`x:16`, `x::float`, endianness/signedness) are a separate
  future extension and are rejected here rather than silently mislowered. The
  module must `use Std.Binary` so the emitted primitives resolve.

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Program}

  defp compile!(fn_name, fn_src, mod) do
    src = "mod M\n  use Std.Binary\n" <> fn_src <> "\nend\n"
    assert {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    assert {:ok, m} =
             Emit.compile_and_load(env, module: mod, functions: [fn_name], origins: origins)

    m
  end

  test "a byte binary literal builds the corresponding BEAM binary" do
    m =
      compile!(
        :build,
        "  fn build() -> Binary = <<1, 2, 3>>",
        :"Cure.Test.BinBuild"
      )

    assert apply(m, :build, []) == <<1, 2, 3>>
  end

  test "a head-byte + rest::binary pattern binds both, guarded by length" do
    m =
      compile!(
        :head,
        """
          fn head(b: Binary) -> Int =
            match b
              <<a, _rest::binary>> -> a
              _ -> 0
        """,
        :"Cure.Test.BinHead"
      )

    assert apply(m, :head, [<<7, 8, 9>>]) == 7
    assert apply(m, :head, [<<42>>]) == 42
    # empty binary → too short → fallthrough
    assert apply(m, :head, [<<>>]) == 0
  end

  test "the rest::binary tail binds the remaining suffix" do
    m =
      compile!(
        :tail,
        """
          fn tail(b: Binary) -> Binary =
            match b
              <<_a, rest::binary>> -> rest
              _ -> b
        """,
        :"Cure.Test.BinTail"
      )

    assert apply(m, :tail, [<<1, 2, 3>>]) == <<2, 3>>
    assert apply(m, :tail, [<<9>>]) == <<>>
  end

  test "a literal byte position becomes an equality guard" do
    m =
      compile!(
        :classify,
        """
          fn classify(b: Binary) -> Int =
            match b
              <<0, _rest::binary>> -> 1
              <<_x, _rest::binary>> -> 2
              _ -> 0
        """,
        :"Cure.Test.BinLit"
      )

    assert apply(m, :classify, [<<0, 5>>]) == 1
    assert apply(m, :classify, [<<5, 0>>]) == 2
    assert apply(m, :classify, [<<>>]) == 0
  end

  test "a fixed-length binary pattern with no tail matches the exact length" do
    m =
      compile!(
        :pair,
        """
          fn pair(b: Binary) -> Int =
            match b
              <<x, y>> -> x + y
              _ -> 0
        """,
        :"Cure.Test.BinPair"
      )

    assert apply(m, :pair, [<<3, 4>>]) == 7
    # three bytes → not an exact 2-byte match → fallthrough
    assert apply(m, :pair, [<<3, 4, 5>>]) == 0
    assert apply(m, :pair, [<<3>>]) == 0
  end

  test "a binary match with no default arm is rejected" do
    src = """
    mod M
      use Std.Binary
      fn f(b: Binary) -> Int =
        match b
          <<a, _rest::binary>> -> a
    end
    """

    assert {:error, {:source_context, {:binary_match_needs_default}, _}} = Program.elaborate(src)
  end
end
