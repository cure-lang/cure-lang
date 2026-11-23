defmodule Cure.Elab.ProofAdmissionTest do
  use ExUnit.Case, async: false

  alias Cure.Core.Env
  alias Cure.Elab.{Program, ProofAdmission}

  defp false_proof(definitions, command, decorator \\ "") do
    definitions = definitions |> String.trim() |> String.replace("\n", "\n  ")

    """
    mod ProofAdmissionAudit
      use Std.Equivalent
      use Std.Nat

      #{definitions}

      #{decorator}
      fn theorem() -> Equivalent(Nat, Z(), S(Z())) = proof chain
        Z() == S(Z())
        because #{command}
    end
    """
  end

  defp assert_admission_refusal(source, opts \\ []) do
    file = Keyword.get(opts, :file, "proof-admission-audit.cure")
    opts = Keyword.put(opts, :file, file)

    assert {:error, error} = Cure.Compiler.check_source(source, opts)
    assert {:proof_totality_required, _name} = Program.semantic_error(error)

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, file, source)
    assert diagnostic.code == "E013"
    assert diagnostic.key == :proof_totality_unproven
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 120)
    assert rendered =~ "logical proof"
    refute rendered =~ "is marked `@total true`"

    assert {:error, release_error} = Cure.Compiler.compile_and_load(source, opts)
    assert {:codegen_error, {:proof_totality_required, _name}} = Program.semantic_error(release_error)
    {release_diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic(release_error, file, source)
    assert release_diagnostic.code == "E013"
  end

  test "self recursion is not admitted as exact evidence for a false equality" do
    false_proof(
      "fn loop() -> Equivalent(Nat, Z(), S(Z())) = loop()",
      "exact loop()"
    )
    |> assert_admission_refusal()
  end

  test "mutually recursive evidence is refused through the actual release path" do
    false_proof(
      """
      fn left() -> Equivalent(Nat, Z(), S(Z())) = right()
      fn right() -> Equivalent(Nat, Z(), S(Z())) = left()
      """,
      "exact left()"
    )
    |> assert_admission_refusal()
  end

  test "an explicit partial annotation does not waive a proof admission requirement" do
    false_proof(
      "fn loop() -> Equivalent(Nat, Z(), S(Z())) = loop()",
      "exact loop()",
      "@total false"
    )
    |> assert_admission_refusal()
  end

  test "a partial imported helper cannot become evidence merely by crossing an interface" do
    dir = Path.join(System.tmp_dir!(), "cure-proof-admission-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)

    File.write!(Path.join(dir, "provider.cure"), """
    mod PartialProofProvider
      use Std.Equivalent
      use Std.Nat
      fn loop() -> Equivalent(Nat, Z(), S(Z())) = loop()
    end
    """)

    source = """
    mod ProofAdmissionAudit
      use PartialProofProvider
      use Std.Equivalent
      use Std.Nat
      fn theorem() -> Equivalent(Nat, Z(), S(Z())) = proof chain
        Z() == S(Z())
        because exact loop()
    end
    """

    assert_admission_refusal(source, file: Path.join(dir, "consumer.cure"), source_roots: [dir])
  end

  test "ordinary partial runtime computation remains legal without executing it" do
    source = """
    mod PartialRuntimeCompatibility
      fn loop(n: Int) -> Int = loop(n)
    end
    """

    assert {:ok, env} = Cure.Compiler.check_source(source)
    refute Env.total?(env, :"PartialRuntimeCompatibility#loop")
    assert {:ok, :"Cure.PartialRuntimeCompatibility"} = Cure.Compiler.compile_and_load(source)
  end

  test "development holes remain checkable but never releasable" do
    source = """
    mod ProofAdmissionHole
      use Std.Equivalent
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because ?later
    end
    """

    assert {:ok, _env} = Cure.Compiler.check_source(source)
    assert {:error, error} = Cure.Compiler.compile_and_load(source)
    {diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic(error, "nofile", source)
    assert diagnostic.code == "E014"
  end

  test "completed ordinary evidence receives an existing kernel totality certificate" do
    source = """
    mod ProofAdmissionPositive
      use Std.Equivalent
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because exact reflexive(x)
    end
    """

    assert {:ok, env} = Cure.Compiler.check_source(source)
    assert Env.total?(env, :"ProofAdmissionPositive#theorem")
    assert {:ok, :"Cure.ProofAdmissionPositive"} = Cure.Compiler.compile_and_load(source)
  end

  test "quoted proof syntax is data, not an executed proof requirement" do
    refute ProofAdmission.execution?({:quoted_syntax, [], [{:proof_chain, [], []}]})
    assert ProofAdmission.execution?({:tactic_computed_use, [], []})
    assert ProofAdmission.execution?({:tactic_script, [], [{:proof_application, [], []}]})
  end

  test "an anonymous search hole cannot hide divergent lemma evidence" do
    assert_admission_refusal("""
    mod ProofAdmissionAudit
      use Std.Equivalent
      use Std.Nat
      @lemma
      fn loop() -> Equivalent(Nat, Z(), S(Z())) = loop()
      fn theorem() -> Equivalent(Nat, Z(), S(Z())) = ?
    end
    """)
  end

  test "automatic refinement search cannot hide divergent lemma evidence" do
    assert_admission_refusal("""
    mod ProofAdmissionAudit
      use Std.Equivalent
      use Std.Nat
      use Std.Refine
      @lemma
      fn loop() -> Equivalent(Nat, Z(), S(Z())) = loop()
      fn theorem() -> {value: Nat | Equivalent(Nat, Z(), S(Z()))} = Z()
    end
    """)
  end

  test "successful implicit local search retains ordinary total proof evidence" do
    source = """
    mod ImplicitProofAdmissionPositive
      use Std.Equivalent
      fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Int, x, y) = ?
    end
    """

    assert {:ok, env} = Cure.Compiler.check_source(source)
    assert :"ImplicitProofAdmissionPositive#theorem" in Env.required_totals(env)
    assert Env.total?(env, :"ImplicitProofAdmissionPositive#theorem")
    assert {:ok, :"Cure.ImplicitProofAdmissionPositive"} = Cure.Compiler.compile_and_load(source)
  end

  test "automatic refinement with genuine local evidence still compiles" do
    source = """
    mod RefinementProofAdmissionPositive
      use Std.Equivalent
      use Std.Nat
      use Std.Refine
      fn theorem(x: Nat, h: Equivalent(Nat, x, x)) -> {value: Nat | Equivalent(Nat, value, x)} = x
    end
    """

    assert {:ok, env} = Cure.Compiler.check_source(source)
    assert Env.total?(env, :"RefinementProofAdmissionPositive#theorem")
    assert {:ok, :"Cure.RefinementProofAdmissionPositive"} = Cure.Compiler.compile_and_load(source)
  end

  test "discarded overload candidates do not impose proof requirements on ordinary partial code" do
    source = """
    mod SpeculativeProofAdmission
      use Std.Equivalent
      use Std.Nat
      use Std.Refine
      @lemma
      fn evidence_loop() -> Equivalent(Nat, Z(), S(Z())) = evidence_loop()
      fn pick(value: {n: Nat | Equivalent(Nat, Z(), S(Z()))}, other: Nat) -> Int = 0
      fn pick(value: Nat, other: String) -> Int = 1
      fn runtime_loop(n: Int) -> Int = runtime_loop(n)
      fn theorem() -> Int = runtime_loop(pick(Z(), "chosen"))
    end
    """

    assert {:ok, env} = Cure.Compiler.check_source(source)
    refute :"SpeculativeProofAdmission#theorem" in Env.required_totals(env)
    refute Env.total?(env, :"SpeculativeProofAdmission#theorem")
    assert {:ok, :"Cure.SpeculativeProofAdmission"} = Cure.Compiler.compile_and_load(source)
  end

  test "admission effects are isolated by speculation, nesting and exceptions" do
    assert {:discarded, false} =
             ProofAdmission.capture(fn ->
               assert {{:ok, :candidate}, true} =
                        ProofAdmission.speculate(fn -> ProofAdmission.observe_result({:ok, :candidate}) end)

               :discarded
             end)

    assert {:committed, true} =
             ProofAdmission.capture(fn ->
               assert {{:ok, :candidate}, used?} =
                        ProofAdmission.speculate(fn -> ProofAdmission.observe_result({:ok, :candidate}) end)

               ProofAdmission.commit(used?)

               assert {:nested, false} = ProofAdmission.capture(fn -> :nested end)
               :committed
             end)

    assert_raise RuntimeError, fn ->
      ProofAdmission.capture(fn ->
        ProofAdmission.observe_result({:ok, :candidate})
        raise "discard this failed scope"
      end)
    end

    assert {:fresh, false} = ProofAdmission.capture(fn -> :fresh end)
  end
end
