defmodule Cure.Compiler.MacroExpansionCompilerEntrySoundnessTest do
  @moduledoc """
  Soundness firewall for the public `Cure.Compiler.compile_string/2` entry.

  The compiler has one dependent pipeline, but its high-level entry still needs
  an explicit regression guard: generated expansions and their handwritten
  equivalents must receive the same elaborator/kernel verdict.
  """

  use ExUnit.Case, async: true

  alias Cure.Compiler

  defp verdict(src) do
    case Compiler.compile_string(src, []) do
      {:ok, _module, _forms} -> :accept
      {:error, term} -> {:reject, Cure.Elab.Program.semantic_error(term)}
    end
  end

  @cases [
    {"zero-hole accept", "mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n",
     "mod M\n  fn f() -> Int = 0\n"},
    {"one-hole accept", "mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n  fn f(n: Int) -> Int = inc n\n",
     "mod M\n  fn f(n: Int) -> Int = n + 1\n"},
    {"unknown global rejection",
     "mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n  fn f() -> Int = bad\n",
     "mod M\n  fn f() -> Int = nonexistent_thing\n"},
    {"type mismatch rejection", "mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n",
     "mod M\n  fn f() -> Int = true\n"}
  ]

  for {label, macro_src, handwritten_src} <- @cases do
    test "compiler-entry macro verdict equals handwritten verdict: #{label}" do
      assert verdict(unquote(macro_src)) == verdict(unquote(handwritten_src))
    end
  end

  test "the compiler entry genuinely accepts and rejects in the expected direction" do
    assert :accept = verdict("mod M\n  macro Zero\n    syntax zero becomes 0\n  fn f() -> Int = zero\n")

    assert {:reject, _} =
             verdict("mod M\n  macro T\n    syntax tt becomes true\n  fn f() -> Int = tt\n")
  end

  test "ill-typed generated examples fail at macro validation" do
    source =
      "mod M\n  macro Bad\n    syntax bad <n: Nat> becomes n + true\n  fn f() -> Int = 0\n"

    assert {:reject, {:expansion_ill_typed, _}} = verdict(source)
  end
end
