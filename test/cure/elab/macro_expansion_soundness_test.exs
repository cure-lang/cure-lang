# test/cure/elab/macro_expansion_soundness_test.exs
defmodule Cure.Elab.MacroExpansionSoundnessTest do
  # SOUNDNESS FIREWALL for the Program.elaborate/1 entry point: a macro's
  # expansion is type-checked exactly like hand-written code there — expansion
  # is a parse-time surface-AST rewrite, so the *unchanged* elaborator+kernel
  # judges it (TCB delta zero for this call). This test proves it by
  # verdict-equality: each macro program elaborates to the IDENTICAL result as
  # the hand-written program it expands to — accepting when well-typed, and
  # rejecting with the SAME error term when ill-typed (well-formed-but-mistyped
  # included). If a future change ever lets macro output reach codegen without
  # full elaboration, one of these equalities breaks. The public compiler entry
  # is guarded separately by the compiler-entry soundness suite.
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # Reduce an elaborate result to a position-free comparable verdict. Accept
  # collapses to :accept (the Env is large and not meaningfully ==); reject
  # keeps its error term verbatim (the terms exercised here carry no line/col).
  defp verdict(src) do
    case Program.elaborate(src) do
      {:ok, _env} -> :accept
      {:error, term} -> {:reject, Program.semantic_error(term)}
    end
  end

  # {label, macro_program, hand_written_equivalent}. Each macro_program's
  # expansion is textually the hand_written_equivalent's body.
  @cases [
    {"zero-hole accept: zero => 0",
     "mod M\n  macro Zero\n    syntax zero becomes 0\n      example zero expands 0\n    explain\n      keyword \"zero\" =>\n        \"starts with zero\"\n  fn f() -> Int = zero\n",
     "mod M\n  fn f() -> Int = 0\n"},
    {"one-hole accept: inc <x> => x + 1",
     "mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n      example inc 1 expands 1 + 1\n    explain\n      Code =>\n        \"expects code\"\n      keyword \"inc\" =>\n        \"starts with inc\"\n  fn f(n: Int) -> Int = inc n\n",
     "mod M\n  fn f(n: Int) -> Int = n + 1\n"},
    {"reject (unknown global): bad => nonexistent_thing",
     "mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n      example bad expands nonexistent_thing\n    explain\n      keyword \"bad\" =>\n        \"starts with bad\"\n  fn f() -> Int = bad\n",
     "mod M\n  fn f() -> Int = nonexistent_thing\n"},
    {"reject (type mismatch): tt => true used as Int",
     "mod M\n  macro T\n    syntax tt becomes true\n      example tt expands true\n    explain\n      keyword \"tt\" =>\n        \"starts with tt\"\n  fn f() -> Int = tt\n",
     "mod M\n  fn f() -> Int = true\n"}
  ]

  for {label, macro_src, hand_src} <- @cases do
    test "macro verdict equals hand-written verdict — #{label}" do
      assert verdict(unquote(macro_src)) == verdict(unquote(hand_src))
    end
  end

  # Pin the accept/reject SENSE too, so an implementation that made *both* sides
  # equally broken (e.g. every program rejects) can't pass by trivial equality.
  test "the two well-typed cases genuinely accept" do
    assert verdict(
             "mod M\n  macro Zero\n    syntax zero becomes 0\n      example zero expands 0\n    explain\n      keyword \"zero\" =>\n        \"starts with zero\"\n  fn f() -> Int = zero\n"
           ) == :accept

    assert verdict(
             "mod M\n  macro Inc\n    syntax inc <x: Code> becomes x + 1\n      example inc 1 expands 1 + 1\n    explain\n      Code =>\n        \"expects code\"\n      keyword \"inc\" =>\n        \"starts with inc\"\n  fn f(n: Int) -> Int = inc n\n"
           ) ==
             :accept
  end

  test "the two ill-typed cases genuinely reject with a position-free error term" do
    assert {:reject, {:unknown_global, :nonexistent_thing, _details}} =
             verdict(
               "mod M\n  macro Bad\n    syntax bad becomes nonexistent_thing\n      example bad expands nonexistent_thing\n    explain\n      keyword \"bad\" =>\n        \"starts with bad\"\n  fn f() -> Int = bad\n"
             )

    # `true` (Std.Bool#True) checked against the return type `Int` — now the
    # inductive `Std.Int#Int` family — is rejected by ctor-membership: True is
    # not one of Int's constructors, so the error is the position-free
    # `{:foreign_ctor, …}` rather than a bare conversion_failure against the
    # retired `{:int_type}` facade. Still a genuine rejection.
    assert {:reject, {:foreign_ctor, :"Std.Bool#True"}} =
             verdict(
               "mod M\n  macro T\n    syntax tt becomes true\n      example tt expands true\n    explain\n      keyword \"tt\" =>\n        \"starts with tt\"\n  fn f() -> Int = tt\n"
             )
  end
end
