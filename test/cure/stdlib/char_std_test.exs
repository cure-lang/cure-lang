defmodule Cure.Stdlib.CharStdTest do
  @moduledoc """
  `Std.Char` gives the `Char` type a visible, documented home. `Char` began as a
  typealias buried inside `Std.Binary` (`use Std.Char` was a silently-tolerated
  no-op resolving to nothing), then became a public `typealias Char =
  Bounded(0x110000)` here; it is now a nominal `@builtin(:char) opaque type`, so
  an arbitrary bounded value can no longer be passed where a character is
  expected. This pins that `Std.Char` owns the *nominal family*, that it erases
  to a bare code-point integer, and that `Std.Binary` still defers to it.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Inductive
  alias Cure.Elab.Program

  test "Std.Char owns the nominal Char family, opaque and integer-erased" do
    assert {:ok, env} = Program.elaborate(File.read!("lib/std/char.cure"))
    assert %{name: :"Std.Char#Char", level: 0, opaque: true, erasure: :integer} = char_family(env)
  end

  test "Char is ambient: it resolves with no `use Std.Char` at all" do
    # `Char` carries `@prelude`, like `String`, so a bare `Char` in a signature
    # resolves through the prelude rather than through an import.
    src = "mod M\n  fn f(c: Char) -> Char = c\nend\n"
    {:ok, env} = Program.elaborate(src)
    assert %{name: :"Std.Char#Char", opaque: true} = char_family(env)
  end

  test "Char has no constructor: values come only from literals and the checked boundary" do
    assert {:ok, env} = Program.elaborate(File.read!("lib/std/char.cure"))
    assert Inductive.opaque?(env, :Char)
    refute Enum.any?(env.ctor_to_family, fn {_ctor, family} -> family == :"Std.Char#Char" end)
  end

  test "Std.Binary re-uses Std.Char rather than redefining Char" do
    # binary.cure must NOT carry its own `typealias Char`; it imports Std.Char.
    src = File.read!("lib/std/binary.cure")
    refute src =~ ~r/typealias\s+Char\b/
    assert src =~ ~r/use\s+Std\.Char\b/
  end

  defp char_family(env), do: Inductive.get_family(env, :Char)
end
