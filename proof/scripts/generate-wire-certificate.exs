# Run with:
# elixir -pa _build/test/lib/cure/ebin proof/scripts/generate-wire-certificate.exs [--check]
# Generation only: no Mix startup, ExUnit, kernel checker or stdlib gate.
root = Path.expand("../..", __DIR__)
Code.compiler_options(ignore_module_conflict: true)

for source <- [
      "lib/cure/core/proof_wire.ex",
      "lib/cure/core/proof_recipe.ex",
      "lib/cure/core/proof_snapshot.ex",
      "test/support/proof_snapshot_fixture.ex",
      "test/support/proof_recipe_fixture.ex"
    ] do
  Code.compile_file(Path.join(root, source))
end

{:ok, snapshot} =
  Cure.Core.ProofSnapshot.to_agda(Cure.Test.ProofSnapshotFixture.environment(), "Fixtures.ExecutableSnapshot")

if File.read!(Path.join(root, "proof/Fixtures/ExecutableSnapshot.agda")) != snapshot,
  do: raise("paired source snapshot differs; review its representation boundary")

{:ok, generated} = Cure.Test.ProofRecipeFixture.to_agda()
target = Path.join(root, "proof/Fixtures/ExecutableCertificate.agda")

case System.argv() do
  [] ->
    File.write!(target, generated)
    IO.puts("Generated #{Path.relative_to(target, root)}")

  ["--check"] ->
    if File.read!(target) != generated, do: raise("certificate artifact differs; regenerate it")
    IO.puts("Certificate artifact is byte-for-byte reproducible")

  _other ->
    raise ArgumentError, "expected no arguments or --check"
end
