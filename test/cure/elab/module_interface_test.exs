defmodule Cure.Elab.ModuleInterfaceTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.ModuleInterface
  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program

  @moduletag :tmp_dir

  test "module_interface/2 returns canonical declarations and source identity for a stdlib module" do
    path = "lib/std/core.cure"
    assert {:ok, %ModuleInterface{} = iface} = Program.module_interface("Std.Core", path)
    assert is_nil(iface.export_env)
    assert is_nil(iface.owned_env)
    assert is_map(iface.canonical_declarations)
    assert is_map(iface.canonical_declarations.direct_call_summaries)
    assert iface.canonical_declarations.direct_call_summaries != %{}

    assert {:ok, %Cure.Core.Env{} = restored} =
             Cure.Compiler.ModulePipeline.Interface.to_env(iface)

    assert restored.direct_call_summaries ==
             iface.canonical_declarations.direct_call_summaries

    assert restored.totality_component_of ==
             iface.canonical_declarations.totality_component_of

    assert is_binary(iface.source_hash) and byte_size(iface.source_hash) == 32
    assert is_binary(iface.interface_hash) and byte_size(iface.interface_hash) == 32
    assert :ok = ModuleInterface.validate(iface)
  end

  test "dependency interface identities are canonical and complete" do
    assert {:ok, %ModuleInterface{} = iface} =
             Program.module_interface("Std.Regex", "lib/std/regex.cure")

    assert iface.dependency_interface_hashes != %{}

    assert Enum.all?(iface.dependency_interface_hashes, fn {module_name, hash} ->
             is_binary(module_name) and is_binary(hash) and byte_size(hash) == 32
           end)

    interface_dependencies = Enum.reject(iface.dependency_names, &Cure.Compiler.ModuleIndex.compiler_owned?/1)

    assert Enum.sort(Map.keys(iface.dependency_interface_hashes)) ==
             Enum.sort(interface_dependencies)
  end

  test "module_interface/2 is a cache hit after priming (identical stored term)" do
    path = "lib/std/core.cure"
    # Prime: the first call computes and `:persistent_term.put`s the interface,
    # returning the freshly-computed heap term (put keeps the original, get hands
    # back the off-heap copy — so a compute call is never `:erts_debug.same` as a
    # later read). Every call thereafter is a pure cache read.
    assert {:ok, _primed} = Program.module_interface("Std.Core", path)
    assert {:ok, a} = Program.module_interface("Std.Core", path)
    assert {:ok, b} = Program.module_interface("Std.Core", path)
    # Two cache reads of the same key return the identical off-heap term, proving
    # the stdlib interface is served from the persistent_term cache, not recomputed.
    assert :erts_debug.same(a, b)
  end

  test "one check verifies a canonical artifact generation at most once" do
    mfa = {Cure.Compiler.Artifacts, :verify_artifact, 3}
    :erlang.trace_pattern(mfa, true, [:local, :call_count])

    on_exit(fn -> :erlang.trace_pattern(mfa, false, [:local, :call_count]) end)

    source = """
    mod CanonicalGenerationVerification
      use Std.Syntax
      fn build() -> MacroResult = Expanded(Leaf(:literal, [], SInt(7)))
    """

    assert {:ok, _env} = Program.elaborate(source)
    assert {:call_count, count} = :erlang.trace_info(mfa, :call_count)

    {:ok, set} =
      Cure.Compiler.Artifacts.open_verified_set(
        kind: :stdlib,
        candidates: Cure.Stdlib.Paths.beam_dirs()
      )

    artifact_count =
      set.modules
      |> Map.values()
      |> Enum.flat_map(& &1.artifacts)
      |> length()

    assert count <= artifact_count,
           "one elaboration reverified #{count} artifacts from a #{artifact_count}-artifact generation"
  end

  test "ordinary checking keeps prelude-bootstrap modules out of the ambient prelude" do
    path = Path.expand("lib/std/int.cure")
    source = File.read!(path)
    assert {:ok, tokens} = Lexer.tokenize(source, file: path, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, file: path, emit_events: false)

    assert {:ok, checked} =
             Program.check_ast_artifact(ast,
               source: source,
               file: path,
               module_name: "Std.Int",
               require_module_identity: true
             )

    coherence = checked.env.coherence

    refute coherence && Map.has_key?(coherence.anon, {:Equatable, :"Std.Int#Int"}),
           "Std.Int is in the prelude bootstrap closure and must not auto-derive the ambient Equatable instance"
  end

  test "concurrent cold prelude-manifest readers share one completed value" do
    Program.invalidate_prelude_manifest()

    manifests =
      1..32
      |> Task.async_stream(
        fn _ -> Program.prelude_manifest() end,
        max_concurrency: 32,
        timeout: 30_000,
        ordered: false
      )
      |> Enum.map(fn {:ok, manifest} -> manifest end)

    assert [first | rest] = manifests
    assert first != []
    assert Enum.all?(rest, &(&1 == first))
    assert Program.prelude_manifest() == first
  end

  test "a fresh in-memory loader reuses the fingerprinted interface artifact" do
    path = Path.expand("lib/std/core.cure")
    cache_key = {Program, :module_interface, path}

    # Arrange the artifact this test is about, rather than inheriting one. The
    # fingerprint covers every stdlib source, so it conservatively -- and
    # legitimately -- moves during any run that recompiles one, and an artifact
    # written before such a move no longer validates. A priming call cannot
    # repair that on its own: served from the in-memory memo, it never touches
    # disk at all, and the assertion below then measures whatever an earlier
    # test happened to leave in the OS temporary directory.
    #
    # Erasing the memo FIRST forces priming down the artifact path, which either
    # validates the file already there or recompiles and rewrites it under the
    # current fingerprint.
    :persistent_term.erase(cache_key)
    assert {:ok, primed} = Program.module_interface("Std.Core", path)

    :persistent_term.erase(cache_key)
    Process.put(:cure_module_loader_observer, self())

    on_exit(fn ->
      Process.delete(:cure_module_loader_observer)
    end)

    assert {:ok, cached} = Program.module_interface("Std.Core", path)
    assert cached == primed
    refute_received {:cure_module_loader, {:compiling, "Std.Core", ^path}}
  end

  test "module_interface/2 surfaces an error for a missing file" do
    assert {:error, _} = Program.module_interface("Nope", "lib/std/does_not_exist.cure")
  end

  test "interface dependency edges retain their authored kind and source line", %{tmp_dir: dir} do
    path = Path.join(dir, "interface_edges.cure")

    File.write!(path, """
    mod InterfaceEdges

      use Std.Nat
      fn count() -> Int = Std.Int.negate(1)
    """)

    assert {:ok, interface} = Program.module_interface("InterfaceEdges", path)

    assert Enum.map(interface.direct_edges, &{&1.kind, &1.target, &1.line}) == [
             {:qualified_reference, "Std.Int", 4},
             {:use_import, "Std.Nat", 3}
           ]
  end
end
