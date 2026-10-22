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
      "test/support/proof_snapshot_fixture.ex",
      "test/support/proof_recipe_fixture.ex",
      "test/support/proof_bundle_fixture.ex",
      "test/support/proof_caller_fixture.ex"
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

targets = [
  {Path.join(root, "proof/Fixtures/ExecutableCertificate.agda"), generated},
  {Path.join(root, "proof/Fixtures/ExecutableBundle.agda"), bundle},
  {Path.join(root, "proof/Fixtures/ExecutableCaller.agda"), caller}
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

    IO.puts("Source, certificate and caller artifacts are byte-for-byte reproducible")

  _other ->
    raise ArgumentError, "expected no arguments or --check"
end
