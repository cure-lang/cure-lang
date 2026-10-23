# Run with:
# elixir -pa _build/test/lib/cure/ebin proof/scripts/generate-wire-certificate.exs [--check]
# Generation only: no Mix startup, ExUnit, kernel checker or stdlib gate.
root = Path.expand("../..", __DIR__)
Code.compiler_options(ignore_module_conflict: true)

for source <- [
      "lib/cure/core/proof_wire.ex",
      "lib/cure/core/proof_recipe.ex",
      "lib/cure/core/proof_snapshot.ex",
      "lib/cure/core/proof_snapshot_wire.ex",
      "lib/cure/core/context.ex",
      "lib/cure/core/eval.ex",
      "lib/cure/core/quote.ex",
      "lib/cure/core/normalise.ex",
      "lib/cure/core/conv.ex",
      "lib/cure/core/proof_context.ex",
      "test/support/proof_snapshot_fixture.ex",
      "test/support/proof_recipe_fixture.ex",
      "test/support/proof_bundle_fixture.ex",
      "test/support/proof_caller_fixture.ex",
      "test/support/proof_context_fixture.ex",
      "test/support/proof_closure_fixture.ex",
      "test/support/proof_quotation_fixture.ex",
      "test/support/proof_comparison_fixture.ex",
      "test/support/proof_checking_fixture.ex",
      "test/support/proof_case_fixture.ex",
      "test/support/proof_constructor_fixture.ex",
      "test/support/proof_scrutinee_fixture.ex",
      "test/support/proof_recursive_case_fixture.ex",
      "test/support/proof_case_context_fixture.ex",
      "test/support/proof_data_spine_fixture.ex",
      "test/support/proof_recursive_data_fixture.ex",
      "test/support/proof_branch_opening_fixture.ex",
      "test/support/proof_residual_normal_fixture.ex",
      "test/support/proof_neutral_case_fixture.ex"
    ] do
  Code.compile_file(Path.join(root, source))
end

{:ok, snapshot} =
  Cure.Core.ProofSnapshot.to_agda(Cure.Test.ProofSnapshotFixture.environment(), "Fixtures.ExecutableSnapshot")

if File.read!(Path.join(root, "proof/Fixtures/ExecutableSnapshot.agda")) != snapshot,
  do: raise("paired source snapshot differs; review its representation boundary")

{:ok, generated} = Cure.Test.ProofRecipeFixture.to_agda()
{:ok, bundle} = Cure.Test.ProofBundleFixture.to_agda()
{:ok, caller} = Cure.Test.ProofCallerFixture.to_agda()
{:ok, context} = Cure.Test.ProofContextFixture.to_agda()
{:ok, closure} = Cure.Test.ProofClosureFixture.to_agda()
{:ok, quotation} = Cure.Test.ProofQuotationFixture.to_agda()
{:ok, comparison} = Cure.Test.ProofComparisonFixture.to_agda()
{:ok, checking} = Cure.Test.ProofCheckingFixture.to_agda()
{:ok, cases} = Cure.Test.ProofCaseFixture.to_agda()
{:ok, constructors} = Cure.Test.ProofConstructorFixture.to_agda()
{:ok, scrutinees} = Cure.Test.ProofScrutineeFixture.to_agda()
{:ok, recursive_cases} = Cure.Test.ProofRecursiveCaseFixture.to_agda()
{:ok, case_contexts} = Cure.Test.ProofCaseContextFixture.to_agda()
{:ok, data_spines} = Cure.Test.ProofDataSpineFixture.to_agda()
{:ok, recursive_data} = Cure.Test.ProofRecursiveDataFixture.to_agda()
{:ok, branch_opening} = Cure.Test.ProofBranchOpeningFixture.to_agda()
{:ok, residual_normal} = Cure.Test.ProofResidualNormalFixture.to_agda()
{:ok, neutral_cases} = Cure.Test.ProofNeutralCaseFixture.to_agda()

targets = [
  {Path.join(root, "proof/Fixtures/ExecutableCertificate.agda"), generated},
  {Path.join(root, "proof/Fixtures/ExecutableBundle.agda"), bundle},
  {Path.join(root, "proof/Fixtures/ExecutableCaller.agda"), caller},
  {Path.join(root, "proof/Fixtures/ExecutableContext.agda"), context},
  {Path.join(root, "proof/Fixtures/ExecutableClosure.agda"), closure},
  {Path.join(root, "proof/Fixtures/ExecutableQuotation.agda"), quotation},
  {Path.join(root, "proof/Fixtures/ExecutableComparison.agda"), comparison},
  {Path.join(root, "proof/Fixtures/ExecutableChecking.agda"), checking},
  {Path.join(root, "proof/Fixtures/ExecutableCase.agda"), cases},
  {Path.join(root, "proof/Fixtures/ExecutableConstructor.agda"), constructors},
  {Path.join(root, "proof/Fixtures/ExecutableScrutinee.agda"), scrutinees},
  {Path.join(root, "proof/Fixtures/ExecutableRecursiveCase.agda"), recursive_cases},
  {Path.join(root, "proof/Fixtures/ExecutableCaseContext.agda"), case_contexts},
  {Path.join(root, "proof/Fixtures/ExecutableDataSpine.agda"), data_spines},
  {Path.join(root, "proof/Fixtures/ExecutableRecursiveData.agda"), recursive_data},
  {Path.join(root, "proof/Fixtures/ExecutableBranchOpening.agda"), branch_opening},
  {Path.join(root, "proof/Fixtures/ExecutableResidualNormal.agda"), residual_normal},
  {Path.join(root, "proof/Fixtures/ExecutableNeutralCase.agda"), neutral_cases}
]

case System.argv() do
  [] ->
    for {target, contents} <- targets do
      File.write!(target, contents)
      IO.puts("Generated #{Path.relative_to(target, root)}")
    end

  ["--check"] ->
    for {target, contents} <- targets do
      if File.read!(target) != contents, do: raise("#{Path.relative_to(target, root)} differs; regenerate it")
    end

    IO.puts("All proof source, execution, comparison and checking artifacts are byte-for-byte reproducible")

  _other ->
    raise ArgumentError, "expected no arguments or --check"
end
