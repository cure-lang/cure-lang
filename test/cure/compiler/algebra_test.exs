defmodule Cure.Compiler.AlgebraTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Algebra, Formatter}

  # -- Algebra primitives ----------------------------------------------------

  describe "Cure.Compiler.Algebra" do
    test "empty document renders to empty iodata" do
      assert Algebra.format(Algebra.empty(), 80) |> IO.iodata_to_binary() == ""
    end

    test "concat of strings" do
      doc = Algebra.concat(Algebra.string("hello"), Algebra.string(" world"))
      assert Algebra.format(doc, 80) |> IO.iodata_to_binary() == "hello world"
    end

    test "line emits a newline" do
      doc = Algebra.concat([Algebra.string("a"), Algebra.line(), Algebra.string("b")])
      assert Algebra.format(doc, 80) |> IO.iodata_to_binary() == "a\nb"
    end

    test "nest adds indentation to hard newlines" do
      doc =
        Algebra.concat([
          Algebra.string("outer"),
          Algebra.nest(
            Algebra.concat([Algebra.line(), Algebra.string("inner")]),
            2
          )
        ])

      assert Algebra.format(doc, 80) |> IO.iodata_to_binary() == "outer\n  inner"
    end

    test "group fits flat when under width" do
      doc =
        Algebra.group(
          Algebra.concat([
            Algebra.string("f("),
            Algebra.break(""),
            Algebra.string("x"),
            Algebra.break(""),
            Algebra.string(")")
          ])
        )

      assert Algebra.format(doc, 80) |> IO.iodata_to_binary() == "f(x)"
    end

    test "group breaks when over width" do
      doc =
        Algebra.group(
          Algebra.concat([
            Algebra.string("f("),
            Algebra.nest(
              Algebra.concat([
                Algebra.break(""),
                Algebra.string("very_long_argument_name")
              ]),
              2
            ),
            Algebra.break(""),
            Algebra.string(")")
          ])
        )

      out = Algebra.format(doc, 10) |> IO.iodata_to_binary()
      assert String.contains?(out, "\n")
      assert String.contains?(out, "very_long_argument_name")
    end
  end

  # -- AlgebraFormatter ------------------------------------------------------

  describe "Cure.Compiler.AlgebraFormatter" do
    test "round-trips a module with a comment above a function" do
      source = """
      mod Demo
        # explain foo
        fn foo() -> Int = 1
      """

      {:ok, formatted} = Formatter.format_algebra(source)

      assert String.contains?(formatted, "mod Demo")
      assert String.contains?(formatted, "# explain foo")
      assert String.contains?(formatted, "fn foo()")
    end

    test "preserves standalone top-level comments" do
      source = """
      # header
      mod Demo
        fn foo() -> Int = 1
      """

      {:ok, formatted} = Formatter.format_algebra(source)
      assert String.contains?(formatted, "# header")
    end

    test "degrades to original source when verification fails" do
      # Deliberately broken source (unbalanced delimiters — cannot parse). The
      # algebra formatter must not emit garbage; it must return the original
      # unchanged. (An earlier fixture used the symbol run `*&^`, which the
      # generic-operator lexer now tokenises as a legitimate operator, so it no
      # longer fails to parse — structural breakage exercises the same guard.)
      source = "fn ((("
      {:ok, returned} = Formatter.format_algebra(source)
      assert returned == source
    end
  end
end
