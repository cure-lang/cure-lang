defmodule Cure.Elab.RewriteDiagnosticTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  @preamble "mod M\n  type Nat = Z | S(Nat)\n"

  test "a rewrite in inference position labels its proof, body, and whole expression" do
    source =
      @preamble <>
        "  fn keep(p: Equivalent(Nat, Z, Z)) = rewrite p in Z()\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "rewrite_infer.cure")
    assert :rewrite_requires_expected_type = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REWRITE RESULT NEEDS AN ANNOTATION [E093] ---------------- rewrite_infer.cure

             A rewrite changes the type expected by its body, so Cure must know the
             surrounding result type before it can construct the equality motive. This
             rewrite appears where that type is still being inferred.

             at rewrite_infer.cure:3:39
             3 |   fn keep(p: Equivalent(Nat, Z, Z)) = rewrite p in Z()
               |                                       ^^^^^^^ -    --- this rewrite has no expected result type; this proof determines what the body rewrites; this body must be checked against the rewritten result

             Hint: Add a result annotation to the enclosing declaration, or place this rewrite where an expected type is already known
             """)

    assert diagnostic.payload.kind == :rewrite_requires_expected_type

    repaired = String.replace(source, "rewrite p in ", "")
    assert {:ok, _env} = Program.elaborate(repaired, file: "rewrite_infer.cure")
  end

  test "a non-equality proof labels the proof expression rather than the whole declaration" do
    source =
      @preamble <>
        "  fn bad(n: Nat, m: Nat) -> Equivalent(Nat, m, m) = rewrite n in reflexive(m)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "rewrite_proof.cure")
    assert :rewrite_proof_not_equality = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REWRITE PROOF IS NOT AN EQUALITY [E093] ------------------ rewrite_proof.cure

             The expression after `rewrite` must prove an `Equivalent(T, left, right)`
             proposition. This expression has another type, so it provides no endpoints that
             Cure can substitute in the body.

             at rewrite_proof.cure:3:61
             3 | …ent(Nat, m, m) = rewrite n in reflexive(m)
               |                           ^    ------------ this expression does not prove an equality; this body would be checked after applying the equality

             Hint: Pass an `Equivalent` proof after `rewrite`, or remove `rewrite` if no equality is available
             """)

    assert diagnostic.primary.span.start_column == 61
    assert diagnostic.payload.kind == :rewrite_proof_not_equality

    repaired = String.replace(source, "rewrite n in ", "")
    assert {:ok, _env} = Program.elaborate(repaired, file: "rewrite_proof.cure")
  end

  test "a no-op rewrite distinguishes the valid proof from the unaffected body" do
    source =
      @preamble <>
        "  fn unchanged(p: Equivalent(Nat, Z, Z), m: Nat) -> Equivalent(Nat, m, m) = rewrite p in reflexive(m)\nend\n"

    {diagnostic, registry, error} = diagnostic(source, "rewrite_no_match.cure")
    assert {:rewrite_no_match, _, _, _} = Program.semantic_error(error)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- REWRITE DOES NOT CHANGE THE GOAL [E093] --------------- rewrite_no_match.cure

             The supplied equality is valid, but its left endpoint does not occur in the type
             required by this body. Applying it would leave the goal unchanged.

             at rewrite_no_match.cure:3:85
             3 | …ent(Nat, m, m) = rewrite p in reflexive(m)
               |                           ^    ------------ this equality has no matching occurrence in the goal; this body is checked against the unchanged goal

             Hint: Use an equality whose left endpoint occurs in the expected result, or remove this rewrite
             """)

    assert diagnostic.payload.kind == :rewrite_no_match

    repaired = String.replace(source, "rewrite p in ", "")
    assert {:ok, _env} = Program.elaborate(repaired, file: "rewrite_no_match.cure")
  end

  defp diagnostic(source, file) do
    assert {:error, error} = Program.elaborate(source, file: file)
    {diagnostic, registry} = Errors.to_diagnostic(error, file, source)
    {diagnostic, registry, error}
  end
end
