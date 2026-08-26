defmodule Cure.Elab.StringInterpolationTest do
  @moduledoc """
  String interpolation `"a\#{e}b"` in the dependent pipeline, for String-valued
  holes. It desugars (in the elaborator, before Core) to a right fold of
  `Std.String.concat` over the segments — literal chunks become their own
  nominal-`String` desugaring and each hole is elaborated in check mode against
  `String`. Nothing new reaches the kernel.

  The fold used to go through `Std.Binary.str_concat`, which was typed
  `List(Char) -> List(Char) -> List(Char)`. That was correct only while `String`
  was a typealias for `List(Char)`. Once `String` became nominal
  (`rec String { characters: List(Char) }`), literal chunks started elaborating
  to `String` while `str_concat` still demanded `List(Char)`, so *every*
  interpolation failed — and failed with a nonsense diagnostic, because the
  elaborator tried to read the `String` value as a `List(Char)` constructor
  pattern. Concatenation has one canonical owner, `Std.String.concat`, and
  interpolation now names it.

  Scope: holes must already be `String`. Interpolating a non-string value
  (`"n=\#{count}"` with `count : Int`) is a type error here — automatic
  `show`-based conversion waits on the Show interface (#21).

  Part of the pre-#18 surface-construct port batch (see
  memory pre18-surface-construct-gaps).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Program}

  # `String` is nominal, so it erases to the tagged pair `{:String, code_points}`.
  defp cure_string(text), do: {:String, String.to_charlist(text)}

  defp compile!(fn_name, fn_src, mod) do
    src = "mod M\n" <> fn_src <> "\nend\n"
    assert {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env} = Program.elaborate(src)
    origins = Program.import_origins(ast)

    assert {:ok, m} =
             Emit.compile_and_load(env, module: mod, functions: [fn_name], origins: origins)

    m
  end

  test "interpolation splices a String hole between literal chunks" do
    m =
      compile!(
        :greet,
        ~S|  fn greet(name: String) -> String = "hi #{name}!"|,
        :"Cure.Test.Interp"
      )

    assert apply(m, :greet, [cure_string("bob")]) == cure_string("hi bob!")
  end

  test "interpolation with two holes folds all segments" do
    m =
      compile!(
        :pair,
        ~S|  fn pair(a: String, b: String) -> String = "#{a}-#{b}"|,
        :"Cure.Test.Interp2"
      )

    assert apply(m, :pair, [cure_string("x"), cure_string("y")]) == cure_string("x-y")
  end

  test "interpolation needs no import: String and its concatenation are ambient" do
    # The fold is written by the compiler, not by the module the literal appears
    # in, so it names `Std.String.concat` by canonical key rather than by a
    # qualified surface spelling the module never imported.
    m =
      compile!(
        :shout,
        ~S|  fn shout(name: String) -> String = "#{name}!!"|,
        :"Cure.Test.Interp3"
      )

    assert apply(m, :shout, [cure_string("ada")]) == cure_string("ada!!")
  end

  test "a bare List(Char) hole is a type error: String is nominal" do
    src = ~S"""
    mod M
      fn f(cs: List(Char)) -> String = "x=#{cs}"
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end

  test "a non-String hole is a type error until Show lands" do
    src = ~S"""
    mod M
      fn f(count: Int) -> String = "n=#{count}"
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end
end
