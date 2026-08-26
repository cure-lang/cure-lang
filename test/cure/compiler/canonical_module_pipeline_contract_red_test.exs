defmodule Cure.Compiler.CanonicalModulePipelineContractRedTest do
  use ExUnit.Case, async: true

  @moduletag :canonical_module_pipeline_red
  @moduletag :tmp_dir

  test "one immutable manifest owns canonical identity and dependency availability", %{tmp_dir: dir} do
    provider = write!(dir, "z_provider.cure", "mod Example.Provider\n  fn value() -> Int = 1\n")

    consumer =
      write!(
        dir,
        "a_consumer.cure",
        "mod Example.Consumer\n  fn value() -> Int = Example.Provider.value()\n"
      )

    assert {:ok, left} =
             manifest_call(:build, [
               [consumer, provider],
               [package: "fixture", source_roots: [dir]]
             ])

    assert {:ok, right} =
             manifest_call(:build, [
               [provider, consumer],
               [package: "fixture", source_roots: [dir]]
             ])

    assert manifest_call(:semantic_dump, [left]) == manifest_call(:semantic_dump, [right])
    assert manifest_call(:module_names, [left]) == ["Example.Consumer", "Example.Provider"]

    assert {:ok, dependency} = manifest_call(:fetch, [left, "Example.Provider"])
    assert dependency.identity == {"fixture", "Example.Provider"}

    assert [%{kind: :qualified_reference, target: {"fixture", "Example.Provider"}}] =
             manifest_call(:dependencies, [left, "Example.Consumer"])
  end

  test "the manifest rejects duplicate canonical identities before checking bodies", %{tmp_dir: dir} do
    first = write!(dir, "first.cure", "mod Example.Duplicate\n  fn broken() -> Nope = missing\n")
    second = write!(dir, "second.cure", "mod Example.Duplicate\n  fn other() -> Int = 2\n")

    assert {:error, {:duplicate_module_identity, %{identity: {"fixture", "Example.Duplicate"}, providers: providers}}} =
             manifest_call(:build, [
               [second, first],
               [package: "fixture", source_roots: [dir]]
             ])

    assert providers == Enum.sort([first, second])
  end

  test "the manifest reports missing modules before an invalid consumer body is elaborated", %{
    tmp_dir: dir
  } do
    consumer =
      write!(
        dir,
        "consumer.cure",
        "mod Example.Consumer\n  fn broken() -> DefinitelyNotAType = Example.Missing.value()\n"
      )

    assert {:error,
            {:missing_module,
             %{
               requester: {"fixture", "Example.Consumer"},
               target: {"fixture", "Example.Missing"},
               kind: :qualified_reference,
               span: span
             }}} =
             manifest_call(:build, [
               [consumer],
               [package: "fixture", source_roots: [dir]]
             ])

    assert span.path == consumer
    assert span.line == 2
  end

  test "use visibility and qualified availability are separate projections", %{tmp_dir: dir} do
    provider =
      write!(
        dir,
        "provider.cure",
        "mod Example.Provider\n  fn exported() -> Int = 1\n  local fn hidden() -> Int = 2\n"
      )

    lexical =
      write!(
        dir,
        "lexical.cure",
        "mod Example.Lexical\n  use Example.Provider\n  fn value() -> Int = exported()\n"
      )

    qualified =
      write!(
        dir,
        "qualified.cure",
        "mod Example.Qualified\n  fn value() -> Int = Example.Provider.exported()\n"
      )

    assert {:ok, checked} =
             pipeline_call(:check, [
               [qualified, provider, lexical],
               [module_pipeline: :canonical, package: "fixture", source_roots: [dir]]
             ])

    assert {:ok, lexical_key} =
             pipeline_call(:resolve, [checked, "Example.Lexical", :value, "exported"])

    assert {:ok, qualified_key} =
             pipeline_call(:resolve, [
               checked,
               "Example.Qualified",
               :value,
               "Example.Provider.exported"
             ])

    assert lexical_key == qualified_key
    assert lexical_key == {"fixture", "Example.Provider", :value, "exported"}

    assert {:error, :not_in_lexical_scope} =
             pipeline_call(:resolve, [checked, "Example.Qualified", :value, "exported"])

    assert {:error, :private_declaration} =
             pipeline_call(:resolve, [
               checked,
               "Example.Qualified",
               :value,
               "Example.Provider.hidden"
             ])
  end

  test "a checked interface is sufficient in a clean consumer with no provider source or BEAM", %{
    tmp_dir: dir
  } do
    provider = write!(dir, "provider.cure", "mod Example.Provider\n  fn value() -> Int = 41\n")

    consumer =
      write!(dir, "consumer.cure", "mod Example.Consumer\n  fn value() -> Int = Example.Provider.value() + 1\n")

    artifact_dir = Path.join(dir, "interfaces")

    assert {:ok, build} =
             pipeline_call(:check, [
               [provider],
               [module_pipeline: :canonical, package: "fixture", source_roots: [dir]]
             ])

    assert :ok = pipeline_call(:write_interfaces, [build, artifact_dir])
    File.rm!(provider)

    assert {:ok, clean_build} =
             pipeline_call(:check, [
               [consumer],
               [
                 module_pipeline: :canonical,
                 package: "fixture-client",
                 source_roots: [dir],
                 interface_roots: [artifact_dir],
                 forbid_source_fallback: true,
                 forbid_beam_resolution: true,
                 fresh_environment: true
               ]
             ])

    assert :ok = pipeline_call(:kernel_verify_interfaces, [clean_build])
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end

  defp manifest_call(function, arguments),
    do: apply(Cure.Compiler.ModuleManifest, function, arguments)

  defp pipeline_call(function, arguments),
    do: apply(Cure.Compiler.ModulePipeline, function, arguments)
end
