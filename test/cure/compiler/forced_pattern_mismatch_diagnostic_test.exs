defmodule Cure.Compiler.ForcedPatternMismatchDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  @preamble """
  mod ForcedMismatch
    type Nat = Z | S(Nat)
    type Vec(a: Type) indices (n: Nat)
      vnil : Vec(a, Z)
      vcons : a -> Vec(a, n) -> Vec(a, S(n))
  """

  test "a wrong named dot pattern labels the value, named field, and constructor" do
    source =
      @preamble <>
        """
          fn bad({k: Nat}, v: Vec(Nat, S(k))) -> Nat = match v
            vcons({n = .(S(k))}, head, tail) -> head
        end
        """

    {diagnostic, registry, error} = diagnostic(source)

    assert {:forced_pattern_mismatch, {:ctor, _, _}, {:var, _}} =
             Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- FORCED `N` DOES NOT MATCH `VCONS` [E093] --------------- forced_mismatch.cure

             The dot expression denotes `S(k)`, but matching `vcons` fixes `n` as `k`. A
             forced pattern checks an index already determined by the scrutinee; it cannot
             choose a different value.

             at forced_mismatch.cure:7:16
             7 |     vcons({n = .(S(k))}, head, tail) -> head
               |     ----- ------------- `vcons` fixes the value of `n` from the matched index; this check targets the hidden `n` field
               |                ^^^^^^ this forced value disagrees with the index fixed here

             Hint: Change the dot expression to the value fixed by `vcons`, or bind `n` without a dot when it is not forced
             """)

    assert diagnostic.payload == %{
             kind: :forced_pattern_mismatch,
             constructor: "vcons",
             implicit_name: "n",
             actual: "S(k)",
             expected: "k",
             expectation_origin: :pattern
           }

    lsp = Renderer.lsp(diagnostic, registry)
    assert lsp["range"] == range(6, 15, 6, 21)

    assert Enum.map(lsp["relatedInformation"], & &1["location"]["range"]) == [
             range(6, 10, 6, 23),
             range(6, 4, 6, 9)
           ]
  end

  test "a dot expression equal to the forced index elaborates" do
    source =
      @preamble <>
        """
          fn good({k: Nat}, v: Vec(Nat, S(k))) -> Nat = match v
            vcons({n = .k}, head, tail) -> head
        end
        """

    assert {:ok, _env} = Program.elaborate(source, file: "forced_mismatch.cure")
  end

  defp diagnostic(source) do
    assert {:error, error} = Program.elaborate(source, file: "forced_mismatch.cure")
    {diagnostic, registry} = Errors.to_diagnostic(error, "forced_mismatch.cure", source)
    {diagnostic, registry, error}
  end

  defp range(start_line, start_character, end_line, end_character) do
    %{
      "start" => %{"line" => start_line, "character" => start_character},
      "end" => %{"line" => end_line, "character" => end_character}
    }
  end
end
