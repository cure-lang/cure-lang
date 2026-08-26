defmodule Cure.Elab.StringLiteralTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # `String` is nominal -- `rec String { characters: List(Char) }` -- so a string
  # literal elaborates at type `String`, not at `List(Char)`. `Char` is a
  # `@prelude` builtin that erases to its bare code point and `List` to a BEAM
  # list, so `"abc"` runs to the tagged pair `{:String, [97, 98, 99]}`.
  #
  # Both `String` and `Char` are ambient, so nothing here declares them; the
  # `use Std.String` is only for `characters/1` below.
  defp run(body, return_type \\ "String") do
    src = """
    mod S
      use Std.String
      fn t() -> #{return_type} = #{body}
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.S", functions: [:t])
    apply(m, :t, [])
  end

  test ~s|"abc" elaborates to a String and runs to {:String, [97, 98, 99]}| do
    assert run(~s|"abc"|) == {:String, [97, 98, 99]}
  end

  test ~s|the empty string "" wraps the empty charlist| do
    assert run(~s|""|) == {:String, []}
  end

  test ~s|"abc" carries the same code points as the char-literal list ['a', 'b', 'c']| do
    # Nominality means `"abc"` is NOT definitionally `['a', 'b', 'c']` -- that was
    # true only while `String` was a typealias. `characters/1` projects the single
    # field the two now share.
    assert run(~s|Std.String.characters("abc")|, "List(Char)") ==
             run(~s|['a', 'b', 'c']|, "List(Char)")
  end

  test "a multi-byte UTF-8 string decodes by Unicode codepoint" do
    # é = U+00E9 = 233, 😀 = U+1F600 = 128512 — one Char each, not their UTF-8 bytes.
    assert run(~s|"é😀"|) == {:String, [233, 128_512]}
  end
end
