defmodule Cure.Elab.CharPatternTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  # Char literal PATTERNS (`match c | 'a' -> …`). `Char = Bounded(0x110000)`, an
  # indexed family that erases to a native int, so a char-pattern chain lowers
  # like the Int/Float/Bool literal chains — but the per-arm equality test is the
  # polymorphic `struct_eq` (Bounded is not one of the monomorphic int/float/bool
  # twins). `Char` is not yet a prelude type (#29), so the module aliases it
  # locally, exactly as the char-literal and string-literal tests do.
  defp classify(char) do
    src = """
    mod CP
      use Std.Bounded
      typealias Char = Bounded(1114112)
      fn classify(c: Char) -> Int = match c
        'a' -> 1
        'b' -> 2
        x -> 0
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.CP", functions: [:classify])
    apply(m, :classify, [char])
  end

  test "char literal patterns dispatch on codepoint; the catch-all takes the rest" do
    assert classify(?a) == 1
    assert classify(?b) == 2
    assert classify(?z) == 0
  end

  test "char literal patterns unfold the ambient Std.Char alias" do
    src = """
    mod AmbientCharPattern
      use Std.Char

      fn classify(c: Char) -> Int = match c
        '\\n' -> 1
        _ -> 0
    end
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.AmbientCharPattern", functions: [:classify])

    assert apply(mod, :classify, [?\n]) == 1
    assert apply(mod, :classify, [?x]) == 0
  end
end
