defmodule Cure.Stdlib.StringListCharTest do
  @moduledoc """
  #29 — `String` is a value-surface text type over Unicode code points, not the
  old Erlang binary. Pins that string.cure elaborates on the dependent pipeline
  and that its functions run end-to-end (length as code-point count, concat as
  append).

  `String` used to *be* `List(Char)`: a typealias, definitionally equal, so a
  string literal checked against `List(Char)` and `concat` returned a bare
  charlist. It is now nominal — `rec String { characters: List(Char) }` — so the
  two types are distinct and carry distinct conformances (`Equatable`,
  `Comparable`, `Semigroup`, `ExpressibleByStringLiteral` belong to `String`
  alone), and the storage can change later without changing source-level
  identity. `characters/1` and `from_characters/1` are the only bridge, and the
  runtime value is the tagged pair `{:String, charlist}`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "string.cure elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/string.cure"))
  end

  test "char and string literals elaborate with no explicit use Std.Bounded" do
    # Std.Char and Std.String are auto-prelude, so both literal forms resolve
    # everywhere — they are core surface sugar.
    assert {:ok, _} = Program.elaborate("mod M\n  fn c() -> List(Char) = ['a']\nend\n")
    assert {:ok, _} = Program.elaborate("mod M\n  fn s() -> String = \"hi\"\nend\n")
  end

  test "a string literal is a String, not a List(Char)" do
    # The nominal boundary in the direction that matters: the literal protocol
    # belongs to `String`, so `List(Char)` cannot be written as a literal.
    assert {:error, reason} = Program.elaborate("mod M\n  fn s() -> List(Char) = \"hi\"\nend\n")
    assert inspect(reason) =~ "ExpressibleByStringLiteral"
  end

  test "characters/1 and from_characters/1 are the bridge to List(Char)" do
    src = """
    mod M
      use Std.String
      fn round(s: String) -> String = from_characters(characters(s))
      fn codes(s: String) -> List(Char) = characters(s)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "length runs as code-point count" do
    {:ok, env} = Program.elaborate("mod M\n  use Std.String\n  fn n() -> Int = length(\"hello\")\nend\n")
    fns = Program.reachable_def_names(env, [:n])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.StrLen", functions: fns)
    assert apply(m, :n, []) == 5
  end

  test "concat runs as append over the code-point storage" do
    {:ok, env} = Program.elaborate("mod M\n  use Std.String\n  fn c() -> String = concat(\"ab\", \"cd\")\nend\n")
    fns = Program.reachable_def_names(env, [:c])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.StrCat", functions: fns)

    # A `String` erases to the tagged pair; the payload is the charlist.
    assert apply(m, :c, []) == {:String, ~c"abcd"}
  end

  test "the code-point storage is reachable as a bare List(Char)" do
    src = """
    mod M
      use Std.String
      fn c() -> List(Char) = characters(concat("ab", "cd"))
    end
    """

    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [:c])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.StrChars", functions: fns)
    assert apply(m, :c, []) == ~c"abcd"
  end
end
