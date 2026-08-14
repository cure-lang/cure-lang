defmodule Cure.Compiler.CanonicalArtifactIncrementalTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Artifacts, BuildManifest, DepGraph}
  alias Cure.Compiler.Artifacts.Writer

  # A 3-module chain Leaf <- Mid <- Top via `use`, plus `Amb`, an extra module
  # that `Top` `use`s and calls. Surface syntax is the real Cure form
  # (`mod Name` with no `do`/`end`; `fn name(args) -> T = body`), confirmed
  # against `lib/std/*.cure`.
  @leaf_v1 """
  mod Leaf
    fn pubval() -> Int = helper()
    fn helper() -> Int = 1
  """

  # Same source-code definitions, one added comment line -> the elaborated
  # `export_env` (and thus the interface hash) is byte-identical, but the raw
  # source bytes differ. This is the interface-INVARIANT edit: `Leaf` itself
  # recompiles (its `source_hash` changed) but nothing downstream should.
  #
  # NOTE (deviation from plan's `@leaf_v2_private`): a private-helper *body* edit
  # is NOT interface-invariant here — `export_env` carries private def bodies, so
  # changing `helper`'s body changes the hash and legitimately cascades. The
  # plan's Step-4 fallback prescribes exactly this comment/whitespace edit for a
  # language whose `export_env` includes private defs. Verified empirically.
  @leaf_v2_comment """
  mod Leaf
    ## interface-invariant edit: a comment, no change to any definition
    fn pubval() -> Int = helper()
    fn helper() -> Int = 1
  """

  # Changed PUBLIC surface -> interface changed -> use-dependents must recompile.
  @leaf_v3_public """
  mod Leaf
    fn pubval() -> Int = 7
    fn helper() -> Int = 1
    fn newly_exported() -> Int = 3
  """

  @amb_v1 """
  mod Amb
    fn thing() -> Int = 1
  """

  @amb_v2 """
  mod Amb
    fn thing() -> Int = 2
  """

  @mid """
  mod Mid
    use Leaf
    fn midval() -> Int = pubval()
  """

  # Top `use`s Mid (the Leaf<-Mid<-Top chain) and also `use`s Amb, calling it
  # with a qualified name. `Amb` is therefore a direct dependency of `Top`.
  #
  # NOTE (deviation from plan): the plan intended `Top` to call `Amb.thing()`
  # WITHOUT `use Amb`, to exercise a "closure-only" edge (present in
  # `closure_deps_map` but not `order_deps_map`) by having the dependent
  # actually resolve a name ambiently. Empirically, a qualified call to a
  # module that is not `use`d does not compile in this compiler
  # (`{:codegen_error, :unknown_global}`) -- that SPECIFIC construction (ambient
  # NAME RESOLUTION without `use`) cannot be built as a unit fixture. That is
  # not the same claim as "no compilable closure-only edge exists": the edge
  # itself is a purely structural artifact of `DepGraph.finalize_node/4`, which
  # appends every `@prelude`-decorated module to EVERY OTHER node's
  # `closure_deps` unconditionally, regardless of whether that node's body
  # references it at all. A dependent needs no ambient call to pick up the
  # edge -- see the closure-only-edge driver fixture (`P`/`Q`/`R`) further
  # below, which compiles and exercises exactly this. The closure-vs-order
  # superset contract is also pinned by a scan-only test below, and its live
  # effect on the real stdlib (ambient preludes) is exercised by the stdlib
  # integration test (Task 5).
  @top """
  mod Top
    use Mid
    use Amb
    fn topval() -> Int = midval()
    fn viaamb() -> Int = Amb.thing()
  """

  # Two-hop fixture. Certificate identities include member body/summary hashes
  # and dependency hashes, so reverse-dependant invalidation already crosses
  # `Mid` for semantic `Leaf` edits. This fixture additionally changes Mid's
  # inferred result type and checks the same propagation for its public surface.
  #
  # `Mid` omits its return annotation so that `Leaf`'s return type becomes part
  # of `Mid`'s own inferred surface. That specific edit is required: adding a
  # constructor to a `Leaf` type that `Mid` merely returns changes `Leaf`'s
  # interface but NOT `Mid`'s, and the cascade correctly stops -- the same trap
  # recorded for `@leaf_v2_comment` above, verified the same way.
  @chain_leaf_int """
  mod Leaf
    fn pubval() -> Int = 1
  """

  @chain_leaf_nat """
  mod Leaf
    fn pubval() -> Nat = 1
  """

  @chain_mid """
  mod Mid
    use Leaf
    fn midval() = pubval()
  """

  @chain_top """
  mod Top
    use Mid
    fn topval() = midval()
  """

  setup do
    root = Path.join(System.tmp_dir!(), "cure_incr_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    File.mkdir_p!(out)
    on_exit(fn -> File.rm_rf!(root) end)

    write = fn name, body -> File.write!(Path.join(src, name), body) end
    write.("leaf.cure", @leaf_v1)
    write.("mid.cure", @mid)
    write.("top.cure", @top)
    write.("amb.cure", @amb_v1)

    {:ok, src: src, out: out, write: write}
  end

  defp paths(src), do: Path.wildcard(Path.join(src, "*.cure"))

  defp compile(src, out, opts \\ []) do
    canonical_sweep(paths(src), out, Keyword.put_new(opts, :source_roots, [src]))
  end

  defp canonical_sweep(paths, out, opts) do
    kind = Keyword.get(opts, :kind, Keyword.get(opts, :artifact_kind, :project))

    opts =
      opts
      |> Keyword.delete(:artifact_kind)
      |> Keyword.merge(
        module_pipeline: :canonical,
        source_paths: paths,
        output_dir: out,
        kind: kind,
        repair: true
      )

    Artifacts.sweep(opts)
  end

  defp compile_order(graph) do
    order = DepGraph.order_deps_map(graph)
    DepGraph.toposort(order, Map.keys(order), DepGraph.prelude_provider_names(graph))
  end

  defp compiled(result), do: result.rebuilt |> Map.keys() |> Enum.sort()
  defp skipped(result), do: Enum.sort(result.reused)
  defp deleted(result), do: result.removed |> Map.keys() |> Enum.sort()

  defp artifact_root(out), do: Writer.resolve(out)
  defp manifest(out), do: BuildManifest.load(artifact_root(out))

  test "first build compiles every module", %{src: src, out: out} do
    assert {:ok, s} = compile(src, out)
    assert compiled(s) == ["Amb", "Leaf", "Mid", "Top"]
    assert skipped(s) == []
    assert s.errors == []
  end

  test "an interface SCC may mention peer nominal types before either body is checked",
       %{src: src, out: out, write: write} do
    write.(
      "interface_a.cure",
      """
      mod InterfaceA
        use InterfaceB
        rec AValue
          value: Int
        fn accepts_b(value: BValue) -> Int = 1
      """
    )

    write.(
      "interface_b.cure",
      """
      mod InterfaceB
        use InterfaceA
        rec BValue
          value: Int
        fn accepts_a(value: AValue) -> Int = 2
      """
    )

    assert {:ok, summary} = compile(src, out)
    assert summary.errors == []
    assert "InterfaceA" in compiled(summary)
    assert "InterfaceB" in compiled(summary)
    assert File.exists?(Path.join(artifact_root(out), "Cure.InterfaceA.beam"))
    assert File.exists?(Path.join(artifact_root(out), "Cure.InterfaceB.beam"))
  end

  test "progress callback reports each module that actually starts compiling", %{src: src, out: out} do
    owner = self()
    progress = fn event -> send(owner, {:progress, event}) end

    assert {:ok, _summary} = compile(src, out, progress: progress)

    events =
      for _ <- 1..4 do
        assert_receive {:progress, {:compile_started, module, path}}
        assert Path.extname(path) == ".cure"
        module
      end

    assert Enum.sort(events) == ["Amb", "Leaf", "Mid", "Top"]

    assert {:ok, _summary} = compile(src, out, progress: progress)
    refute_receive {:progress, {:compile_started, _, _}}, 50
  end

  test "no-change rebuild compiles nothing", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    assert {:ok, s} = compile(src, out)
    assert compiled(s) == []
    assert skipped(s) == ["Amb", "Leaf", "Mid", "Top"]
  end

  test "incremental edit sequences remain equivalent to clean builds", %{
    src: src,
    out: out,
    write: write
  } do
    edits = [
      fn -> :ok end,
      fn -> write.("leaf.cure", @leaf_v2_comment) end,
      fn -> write.("leaf.cure", @leaf_v3_public) end,
      fn -> write.("extra.cure", "mod Extra\n  fn value() -> Int = 9\n") end,
      fn -> File.rm!(Path.join(src, "extra.cure")) end
    ]

    edits
    |> Enum.with_index()
    |> Enum.each(fn {edit, index} ->
      edit.()
      assert {:ok, incremental} = compile(src, out)
      assert incremental.errors == []

      clean = Path.join(Path.dirname(out), "clean-#{index}")

      assert {:ok, clean_summary} =
               canonical_sweep(paths(src), clean,
                 source_roots: [src],
                 force: true
               )

      assert clean_summary.errors == []
      assert {:ok, incremental_set} = Artifacts.open_verified_set(out, verification: :full)
      assert {:ok, clean_set} = Artifacts.open_verified_set(clean, verification: :full)
      assert semantic_set(incremental_set) == semantic_set(clean_set)
    end)
  end

  test "simultaneous writers serialize and publish one verified generation", %{src: src, out: out} do
    results =
      1..2
      |> Task.async_stream(fn _ -> compile(src, out) end,
        max_concurrency: 2,
        timeout: 120_000
      )
      |> Enum.map(fn {:ok, result} -> result end)

    assert Enum.all?(results, &match?({:ok, %{errors: []}}, &1))
    assert {:ok, _set} = Cure.Compiler.Artifacts.open_verified_set(out)
  end

  test "stale lock metadata does not prevent a kernel lock", %{src: src, out: out} do
    lock = Path.join(out, ".cure_artifact.lock")

    {:ok, host} = :inet.gethostname()

    File.write!(
      lock,
      :erlang.term_to_binary(
        %{
          node: "retired@#{host}",
          pid: "#PID<0.0.0>",
          os_pid: "999999999",
          host: List.to_string(host),
          acquired_at: System.os_time(:second) - 3_601,
          output_root: out,
          intended_generation: :pending
        },
        [:deterministic]
      )
    )

    File.touch!(lock, System.os_time(:second) - 3_601)

    assert {:ok, %{errors: []}} = compile(src, out)
    assert {:ok, _set} = Cure.Compiler.Artifacts.open_verified_set(out)
  end

  test "lock metadata is not mistaken for kernel lock ownership", %{src: src, out: out} do
    lock = Path.join(out, ".cure_artifact.lock")
    {:ok, host} = :inet.gethostname()

    File.write!(
      lock,
      :erlang.term_to_binary(
        %{
          node: "retired@#{host}",
          pid: "#PID<0.0.0>",
          os_pid: "999999999",
          host: List.to_string(host),
          acquired_at: System.os_time(:second),
          output_root: out,
          intended_generation: :pending
        },
        [:deterministic]
      )
    )

    assert {:ok, %{errors: []}} = compile(src, out)
    assert {:ok, _set} = Cure.Compiler.Artifacts.open_verified_set(out)
  end

  test "an abandoned staging generation is removed by the next writer", %{src: src, out: out} do
    abandoned = Path.join(out, ".cure_staging_abandoned")
    File.mkdir_p!(abandoned)
    File.write!(Path.join(abandoned, "partial.beam"), "partial")

    assert {:ok, %{errors: []}} = compile(src, out)
    refute File.exists?(abandoned)
  end

  test "a reader keeps the published generation while a staged writer is interrupted", %{
    src: src,
    out: out
  } do
    assert {:ok, _} = compile(src, out)
    pointer_before = File.read!(Path.join(out, "current"))
    parent = self()

    writer =
      Task.async(fn ->
        Writer.transact(out, fn stage ->
          assert File.regular?(Path.join(stage, BuildManifest.filename()))
          send(parent, {:stage_ready, stage})

          receive do
            :interrupt -> {:error, :injected_interruption}
          end
        end)
      end)

    assert_receive {:stage_ready, stage}, 5_000
    assert {:ok, _set} = Cure.Compiler.Artifacts.open_verified_set(out)
    assert File.read!(Path.join(out, "current")) == pointer_before
    send(writer.pid, :interrupt)
    assert {:error, :injected_interruption} = Task.await(writer)
    refute File.exists?(stage)
    assert File.read!(Path.join(out, "current")) == pointer_before
    assert {:ok, _set} = Cure.Compiler.Artifacts.open_verified_set(out)
  end

  test "editing a leaf's comment (interface-invariant) recompiles only the leaf",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("leaf.cure", @leaf_v2_comment)
    assert {:ok, s} = compile(src, out)
    assert compiled(s) == ["Leaf"]
    assert "Mid" in skipped(s) and "Top" in skipped(s)
  end

  test "editing a public surface invalidates reverse certificate dependants",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("leaf.cure", @leaf_v3_public)
    assert {:ok, s} = compile(src, out)
    assert "Leaf" in compiled(s)
    assert "Mid" in compiled(s)

    assert "Top" in compiled(s),
           "Mid's certificate digest changed with Leaf's dependency identity, so Top must revalidate"
  end

  test "editing a directly-depended module body invalidates its caller certificate",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    write.("amb.cure", @amb_v2)
    assert {:ok, s} = compile(src, out)
    assert "Amb" in compiled(s)
    assert "Top" in compiled(s)
    # Leaf and Mid are outside Amb's reverse-dependency closure.
    assert "Mid" in skipped(s)
    assert "Leaf" in skipped(s)
  end

  test "a change propagates the second hop when the middle module's own interface moves",
       %{src: src, out: out, write: write} do
    write.("leaf.cure", @chain_leaf_int)
    write.("mid.cure", @chain_mid)
    write.("top.cure", @chain_top)

    assert {:ok, first} = compile(src, out)
    assert first.errors == []
    assert "Top" in compiled(first)

    write.("leaf.cure", @chain_leaf_nat)

    assert {:ok, s} = compile(src, out)
    assert s.errors == []

    assert s.rebuilt["Leaf"] == [:source_hash_mismatch]
    assert s.rebuilt["Mid"] == [:dependency_interface_changed]

    # The point of the test: `Top` never mentions `Leaf`, so it can only be
    # reached through `Mid`. Under-rebuilding here would publish a `Top` beam
    # compiled against an interface that no longer exists.
    assert "Top" in compiled(s),
           "Mid's own interface moved, so Top -- which use's only Mid -- must rebuild against it"

    assert s.rebuilt["Top"] == [:dependency_interface_changed]

    # Untouched and unrelated: this is a targeted cascade, not a full rebuild.
    assert "Amb" in skipped(s)
  end

  test "closure_deps_map (the driver's dirty graph) is a strict superset of use-only edges" do
    # The driver decides propagation over `closure_deps_map/1`, not
    # `order_deps_map/1`. This matters for edges that are NOT `use` edges —
    # ambient `@prelude` providers and qualified-call targets — which appear in
    # the closure map only. A dependent that actually RESOLVES a name ambiently
    # (no `use`) is not compilable in this compiler (see the NOTE on `@top`
    # above), so that specific shape is scan-only here; the structural
    # `@prelude`-append edge itself (no ambient call needed) IS compilable and
    # is exercised end-to-end by the `P`/`Q`/`R` driver fixture further below.
    # Scan-only assertion of the superset relationship:
    root = Path.join(System.tmp_dir!(), "cure_closure_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    File.mkdir_p!(src)
    on_exit(fn -> File.rm_rf!(root) end)

    File.write!(Path.join(src, "amb.cure"), "@prelude\nmod Amb\n  @prelude\n  fn thing() -> Int = 1\n")
    File.write!(Path.join(src, "consumer.cure"), "mod Consumer\n  fn go() -> Int = thing()\n")

    {:ok, graph} = DepGraph.scan(Path.wildcard(Path.join(src, "*.cure")))
    closure = DepGraph.closure_deps_map(graph)
    order = DepGraph.order_deps_map(graph)

    # Consumer ambiently depends on Amb: present in closure, absent from order.
    assert "Amb" in Map.get(closure, "Consumer", [])
    refute "Amb" in Map.get(order, "Consumer", [])
  end

  test "a missing beam forces recompile even when the hash matches", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    File.rm!(Path.join(artifact_root(out), "Cure.Leaf.beam"))
    assert {:ok, s} = compile(src, out)
    assert "Leaf" in compiled(s)
  end

  test "a stale Semigroup BEAM cannot be loaded as fresh" do
    root = Path.join(System.tmp_dir!(), "cure_semigroup_stale_#{System.unique_integer([:positive])}")
    src = Path.join(root, "src")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    on_exit(fn -> File.rm_rf!(root) end)

    source = Path.join(src, "semigroup.cure")

    File.write!(source, """
    mod Fixture.Semigroup
      fn current_marker() -> Int = 34
    """)

    assert {:ok, initial} =
             canonical_sweep([source], out,
               source_roots: [src],
               artifact_kind: :stdlib
             )

    assert initial.errors == []
    assert compiled(initial) == ["Fixture.Semigroup"]

    stale_forms = [
      {:attribute, 1, :module, :"Cure.Fixture.Semigroup"},
      {:attribute, 1, :export, [old_marker: 0]},
      {:function, 1, :old_marker, 0, [{:clause, 1, [], [], [{:integer, 1, 25}]}]}
    ]

    stale_result = :compile.forms(stale_forms, [:return, :binary])

    {:ok, :"Cure.Fixture.Semigroup", stale_binary} =
      case stale_result do
        {:ok, module, binary, _warnings} -> {:ok, module, binary}
        {:ok, module, binary} -> {:ok, module, binary}
      end

    File.write!(Path.join(artifact_root(out), "Cure.Fixture.Semigroup.beam"), stale_binary)

    assert {:ok, repaired} =
             canonical_sweep([source], out,
               source_roots: [src],
               artifact_kind: :stdlib
             )

    assert compiled(repaired) == ["Fixture.Semigroup"]
    assert :artifact_hash_mismatch in repaired.rebuilt["Fixture.Semigroup"]

    beam = Path.join(artifact_root(out), "Cure.Fixture.Semigroup.beam")

    {:ok, {:"Cure.Fixture.Semigroup", [exports: exports]}} =
      :beam_lib.chunks(String.to_charlist(beam), [:exports])

    assert {:current_marker, 0} in exports
    refute {:old_marker, 0} in exports
  end

  test "a toolchain change forces a full rebuild", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    m = manifest(out)

    BuildManifest.save(
      %{m | workspace_key: <<0>>, context: Map.put(m.context, :compiler_hash, <<0>>)},
      artifact_root(out)
    )

    assert {:ok, s} = compile(src, out)
    assert compiled(s) == ["Amb", "Leaf", "Mid", "Top"]
  end

  test "deleting a source removes its beam and drops it from the manifest", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    File.rm!(Path.join(src, "top.cure"))
    assert {:ok, s} = compile(src, out)
    assert "Top" in deleted(s)
    refute File.exists?(Path.join(artifact_root(out), "Cure.Top.beam"))
    refute Map.has_key?(manifest(out).modules, "Top")
  end

  test "a toolchain bump in the same build as a deleted source still deletes the beam",
       %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    m = manifest(out)

    BuildManifest.save(
      %{m | workspace_key: <<0>>, context: Map.put(m.context, :compiler_hash, <<0>>)},
      artifact_root(out)
    )

    File.rm!(Path.join(src, "top.cure"))
    assert {:ok, s} = compile(src, out)
    assert "Top" in deleted(s)
    refute File.exists?(Path.join(artifact_root(out), "Cure.Top.beam"))
  end

  test "an unclaimed Cure BEAM is removed instead of entering the next generation", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    File.write!(Path.join(artifact_root(out), "Cure.Std.Fake.beam"), "stub")

    assert {:ok, s} = compile(src, out)
    assert "Cure.Std.Fake.beam" in deleted(s)
    refute File.exists?(Path.join(artifact_root(out), "Cure.Std.Fake.beam"))
    refute Map.has_key?(manifest(out).modules, "Std.Fake")
  end

  test "an unclaimed legacy lowercase BEAM is not carried into a new generation", %{
    src: src,
    out: out
  } do
    assert {:ok, _} = compile(src, out)
    contaminated = artifact_root(out)
    File.write!(Path.join(contaminated, "lists.beam"), "legacy")

    assert {:error, {:artifact_set_invalid, %{orphans: ["lists.beam"]}}} =
             Cure.Compiler.Artifacts.open_verified_set(out)

    assert {:ok, _summary} = compile(src, out)
    refute File.exists?(Path.join(artifact_root(out), "lists.beam"))
    assert {:ok, _set} = Cure.Compiler.Artifacts.open_verified_set(out)
  end

  test "a compile error keeps the module dirty and does not advance the manifest",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    published_before = File.read!(Path.join(out, "current"))
    write.("leaf.cure", "mod Leaf\n  fn pubval() -> Int = nonexistent_fn()\n")
    assert {:error, {:artifact_sweep_failed, diagnostics}} = compile(src, out)
    assert_leaf_unresolved_diagnostic(diagnostics)
    assert File.read!(Path.join(out, "current")) == published_before
    # manifest NOT advanced: next run still sees Leaf as dirty
    assert {:error, {:artifact_sweep_failed, diagnostics2}} = compile(src, out)
    assert_leaf_unresolved_diagnostic(diagnostics2)
  end

  test "a dependency failing to compile treats its dependent as dirty too",
       %{src: src, out: out, write: write} do
    assert {:ok, _} = compile(src, out)
    published_before = File.read!(Path.join(out, "current"))
    # break Leaf; Mid `use`s Leaf. Mid must not be recorded fresh against a broken dep.
    write.("leaf.cure", "mod Leaf\n  fn pubval() -> Int = nonexistent_fn()\n")
    assert {:error, {:artifact_sweep_failed, diagnostics}} = compile(src, out)
    assert_leaf_unresolved_diagnostic(diagnostics)
    assert File.read!(Path.join(out, "current")) == published_before
  end

  defp assert_leaf_unresolved_diagnostic(diagnostics) do
    assert [
             {_path,
              {:unresolved_global,
               %{
                 key: {"root", "Leaf", :value, "nonexistent_fn"},
                 origin: %Cure.Diagnostic.Span{},
                 closure_path: [
                   {"root", "Leaf", :value, "pubval"},
                   {"root", "Leaf", :value, "nonexistent_fn"}
                 ],
                 source_context: %{core_term: {:global, :nonexistent_fn}}
               }}}
           ] = diagnostics
  end

  test "a source with a genuine parse error is reported, not silently dropped", %{src: src, out: out} do
    File.write!(Path.join(src, "broken.cure"), "mod Broken\n  fn x( = end\n")
    assert {:error, {:module_skeleton_error, {"root", "Broken"}, errors}} = compile(src, out)
    assert errors != []
  end

  test "force rebuilds everything", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out)
    assert {:ok, s} = compile(src, out, force: true)
    assert compiled(s) == ["Amb", "Leaf", "Mid", "Top"]
  end

  test "a code-generation option change rebuilds the complete set", %{src: src, out: out} do
    assert {:ok, _} = compile(src, out, compile_opts: [check_types: false])

    assert {:ok, summary} =
             compile(src, out, compile_opts: [check_types: true])

    assert compiled(summary) == ["Amb", "Leaf", "Mid", "Top"]

    assert Enum.all?(summary.rebuilt, fn {_module, reasons} ->
             :compiler_context_mismatch in reasons
           end)
  end

  test "edition, target, OTP, and Elixir context changes rebuild the complete set", %{
    src: src,
    out: out
  } do
    assert {:ok, _} = compile(src, out)

    for field <- [:language_edition, :target, :otp_release, :elixir_version] do
      current = manifest(out)
      changed = %{current | context: Map.put(current.context, field, {:changed, field})}
      BuildManifest.save(changed, artifact_root(out))

      assert {:ok, summary} = compile(src, out)
      assert compiled(summary) == ["Amb", "Leaf", "Mid", "Top"]

      assert Enum.all?(summary.rebuilt, fn {_module, reasons} ->
               :compiler_context_mismatch in reasons
             end)
    end
  end

  test "stdlib and package generation changes rebuild consumers", %{src: src, out: out} do
    assert {:ok, _} =
             compile(src, out,
               stdlib_artifact_digest: <<1>>,
               package_artifact_digests: %{"dep" => <<1>>}
             )

    assert {:ok, summary} =
             compile(src, out,
               stdlib_artifact_digest: <<2>>,
               package_artifact_digests: %{"dep" => <<2>>}
             )

    assert compiled(summary) == ["Amb", "Leaf", "Mid", "Top"]

    assert Enum.all?(summary.rebuilt, fn {_module, reasons} ->
             :dependency_artifact_digest_mismatch in reasons
           end)
  end

  # Proves `beams_for/3` does not over-match on Cure's dotted module-naming
  # convention. `Ns.Base` and `Ns.Base.Child` are two INDEPENDENT top-level
  # modules (two files, two `mod` declarations) that merely share a dotted
  # prefix — mirroring real stdlib siblings like `Std.Otp` / `Std.Otp.Call`.
  # A bare `Cure.Ns.Base.*.beam` wildcard would match `Cure.Ns.Base.Child.beam`
  # too; deleting `Ns.Base`'s source must not delete `Ns.Base.Child`'s beam.
  @ns_base """
  mod Ns.Base
    fn baseval() -> Int = 1
  """

  @ns_base_child """
  mod Ns.Base.Child
    fn childval() -> Int = 2
  """

  test "deleting a module does not delete a sibling whose name shares its dotted prefix",
       %{src: src, out: out, write: write} do
    write.("ns_base.cure", @ns_base)
    write.("ns_base_child.cure", @ns_base_child)
    assert {:ok, s0} = compile(src, out)
    assert "Ns.Base" in compiled(s0) and "Ns.Base.Child" in compiled(s0)

    File.rm!(Path.join(src, "ns_base.cure"))
    assert {:ok, s} = compile(src, out)
    assert "Ns.Base" in deleted(s)
    refute "Ns.Base.Child" in deleted(s)
    assert File.exists?(Path.join(artifact_root(out), "Cure.Ns.Base.Child.beam"))
    assert Map.has_key?(manifest(out).modules, "Ns.Base.Child")
  end

  # Regression (compile-order soundness): the driver must compile every module
  # AFTER its `use`-dependencies (`order_deps`), because codegen links a module's
  # use-deps' beams — build them out of order and a cold build fails with
  # `{:missing_stdlib_module, ...}` (empty code path) or, worse, silently links a
  # STALE dep beam already on the path. The trap: the ambient `@prelude`
  # primitives (`Std.Atom`, `Std.Binary`, `Std.Char`, ...) form a *cycle* in
  # `closure_deps_map/1`, so ordering the walk by the closure graph emits that SCC
  # ALPHABETICALLY — placing `Std.Binary` before `Std.Char` even though
  # `Binary use Char`. `compile_order/1` must instead follow the acyclic
  # `order_deps` graph, exactly as the pre-incremental loop did. This is checked
  # on the real stdlib graph because a compilable ambient cycle can't be built as
  # a bare temp fixture, and the test BEAM keeps the stdlib loaded+sticky (so an
  # in-process cold build resolves deps from memory and can't surface the miss).
  # Regression test for the `dep_changed?/2` not-yet-visited fallback added by
  # the ordering fix (`cae31e7f`). `P` is `@prelude` -- every OTHER module's
  # `closure_deps` gets `P` appended unconditionally (`DepGraph.finalize_node`),
  # regardless of whether it actually references `P`. `P` itself `use`s `R`
  # (a real order_dep), so the acyclic `order_deps` walk schedules `R` before
  # `P`. `Q` has no relationship to `P` at all beyond that ambient closure
  # edge, and no order_dep on anything, so alphabetically it is scheduled
  # BEFORE `P` (`Q` < `R` < `P`). When the driver decides `Q`'s freshness,
  # `P` is not yet in `state.iface` -- the "not-yet-visited closure dep"
  # branch. That branch falls back to `base_dirty[P]`, which reports "clean"
  # (P's own source/beam are untouched) even though P's INTERFACE is about to
  # change this very build, because its real dependency `R` changed. `Q`
  # ambiently depends on `P` (that's what the closure edge means) and must
  # not be served a stale beam.
  @p_prelude """
  @prelude
  mod P
    use R
    fn pval() -> Int = R.val()
  """

  @r_v1 """
  mod R
    fn val() -> Int = 1
  """

  @r_v2 """
  mod R
    fn val() -> Int = 2
  """

  @q_ambient """
  mod Q
    fn qval() -> Int = 42
  """

  test "an ambient consumer rebuilds when its provider certificate identity changes" do
    root = Path.join(System.tmp_dir!(), "cure_ambient_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "src")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    on_exit(fn -> File.rm_rf!(root) end)

    File.write!(Path.join(src, "p.cure"), @p_prelude)
    File.write!(Path.join(src, "r.cure"), @r_v1)
    File.write!(Path.join(src, "q.cure"), @q_ambient)
    paths = Path.wildcard(Path.join(src, "*.cure"))

    assert {:ok, s0} = canonical_sweep(paths, out, source_roots: [src])
    assert compiled(s0) == ["P", "Q", "R"]

    # Prelude providers are prioritized once their explicit dependencies are
    # ready, so P is now visited before its ambient consumer Q without adding a
    # synthetic graph edge.
    {:ok, graph} = DepGraph.scan(paths)
    pos = compile_order(graph) |> Enum.with_index() |> Map.new()
    assert pos["P"] < pos["Q"]

    File.write!(Path.join(src, "r.cure"), @r_v2)
    assert {:ok, s} = canonical_sweep(paths, out, source_roots: [src])

    assert "R" in compiled(s)
    assert "P" in compiled(s),
           "R's body hash changes P's dependency-bound certificate identity"

    assert "Q" in compiled(s),
           "P is an ambient provider, so its certificate change invalidates ambient consumers"
  end

  # Regression: `interface_hash_for/3` recomputes a module's fresh interface via
  # `Program.module_interface/2`, which — for a path recognized as a SHIPPED
  # STDLIB SOURCE — is `:persistent_term`-cached across the WHOLE OS process
  # (`cached_module_interface/2` in `program.ex`: "Shipped stdlib sources are
  # immutable for the lifetime of a compiler run: no test writes them and
  # nothing regenerates them mid-run"). Incremental compilation of the stdlib
  # itself is the first workload to violate that assumption BY DESIGN:
  # `mix cure.compile_stdlib` compiles literal `lib/std/*.cure` paths, and its
  # own regression test (`cure.compile_stdlib_incremental_test.exs`) already
  # `Mix.Task.rerun`s it TWICE in one process. If a stdlib module's source
  # changes between two such same-process runs, `Program.module_interface/2`
  # on the second run silently returns the FIRST run's cached (now-stale)
  # interface — `interface_hash_for/3` computes the SAME hash as before, the
  # driver decides "unchanged", and a real dependent is left `skipped_fresh`
  # even though its dependency's interface genuinely changed on disk.
  #
  # `stdlib_source_path?/1` resolves via `Cure.Stdlib.Paths.source_dir/0`,
  # whose first candidate is the `:stdlib_source_dir` app-env override — the
  # established fixture (see `test/cure/elab/imported_module_dup_test.exs` and
  # siblings) for pointing it at an isolated tmp dir without touching the real
  # `lib/std`. (Verified this is not a BEAM hot-code-loading artifact: the
  # driver's OWN `s2.compiled`/`skipped_fresh` bookkeeping is asserted below,
  # never the runtime behavior of a loaded module.)
  test "a repeated same-process build invalidates consumers across a body-only stdlib edit",
       %{out: out} do
    stdlib_src =
      Path.join(System.tmp_dir!(), "cure_stdlib_cache_#{:erlang.unique_integer([:positive])}")

    File.mkdir_p!(stdlib_src)
    previous = Application.get_env(:cure, :stdlib_source_dir)
    Application.put_env(:cure, :stdlib_source_dir, stdlib_src)

    on_exit(fn ->
      case previous do
        nil -> Application.delete_env(:cure, :stdlib_source_dir)
        value -> Application.put_env(:cure, :stdlib_source_dir, value)
      end

      File.rm_rf!(stdlib_src)
    end)

    r_path = Path.join(stdlib_src, "r.cure")
    p_path = Path.join(stdlib_src, "p.cure")
    File.write!(r_path, "mod R\n  fn val() -> Int = 1\n")
    File.write!(p_path, "mod P\n  use R\n  fn pval() -> Int = R.val()\n")
    paths = Path.wildcard(Path.join(stdlib_src, "*.cure"))

    assert {:ok, s1} = canonical_sweep(paths, out, source_roots: [stdlib_src])
    assert compiled(s1) == ["P", "R"]

    File.write!(r_path, "mod R\n  fn val() -> Int = 2\n")

    assert {:ok, s2} = canonical_sweep(paths, out, source_roots: [stdlib_src])

    assert "R" in compiled(s2)

    assert "P" in compiled(s2),
           "R's changed body hash invalidates P's dependency-bound certificate identity"
  end

  test "compile_order places every module after its use-dependencies (real stdlib graph)" do
    {:ok, graph} = DepGraph.scan(Path.wildcard("lib/std/*.cure"))
    order = compile_order(graph)

    pos = order |> Enum.with_index() |> Map.new()
    order_deps = DepGraph.order_deps_map(graph)

    # "After its use-deps" is a property of the CONDENSATION, not of the raw
    # graph: inside a strongly connected component no such order exists, and the
    # stdlib has one on purpose — `Std.Char` and `Std.String` are mutually
    # recursive, which the canonical pipeline permits via interface skeletons and
    # `DepGraph` reports once as W086. Cycle members compile together in a
    # deterministic order, so the ordering claim applies between components.
    component_of =
      order_deps
      |> DepGraph.components(Map.keys(order_deps))
      |> Enum.with_index()
      |> Enum.flat_map(fn {members, index} -> Enum.map(members, &{&1, index}) end)
      |> Map.new()

    violations =
      for m <- order,
          d <- Map.get(order_deps, m, []),
          Map.has_key?(pos, d),
          component_of[m] != component_of[d],
          pos[d] > pos[m],
          do: {m, d}

    assert violations == [], "module compiled before its use-dep: #{inspect(violations)}"

    # And the exemption is not a blanket one: name the cycles it covers, so a new
    # cycle appearing in the stdlib fails here rather than passing silently.
    cycles =
      order_deps
      |> DepGraph.components(Map.keys(order_deps))
      |> Enum.reject(&match?([_single], &1))

    # `Std.Char` uses `Std.String` and `Std.Literal`; `Std.String` uses both of
    # the others; `Std.Literal` uses `Std.Char` to give `Char` its character
    # literal. One three-member component, and the only one in the stdlib.
    assert cycles == [["Std.Char", "Std.Literal", "Std.String"]]
    # The exact edge that the buggy closure-ordering got wrong.
    assert pos["Std.Char"] < pos["Std.Binary"]
    # Every named stdlib module is scheduled exactly once.
    assert length(order) == map_size(order_deps)
  end

  # LIMITATION 1 (project builds against a non-default output dir never detect a
  # stdlib change). The project-build caller previously fingerprinted
  # `Cure.Std.*.beam` inside the PROJECT's `output_dir`. When that dir is not the
  # one the stdlib actually compiled to, it holds no stdlib beams, so the
  # fingerprint is a constant (hash of the empty list) that never moves when the
  # real stdlib changes — a project module can then be served against a changed
  # stdlib without recompiling. `stdlib_fingerprint/0` resolves the stdlib's real
  # beam location via `Cure.Stdlib.Paths.beam_dir/0` (the `:stdlib_beam_dir`
  # app-env override is its first, highest-priority candidate), independent of
  # any project output dir.
  test "stdlib_fingerprint/0 tracks the resolved stdlib beam dir, not a project output dir" do
    beam_dir = Path.join(System.tmp_dir!(), "cure_stdlib_beams_#{:erlang.unique_integer([:positive])}")
    source_dir = Path.join(System.tmp_dir!(), "cure_stdlib_sources_#{:erlang.unique_integer([:positive])}")
    proj_out = Path.join(System.tmp_dir!(), "cure_proj_out_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(beam_dir)
    File.mkdir_p!(source_dir)
    File.mkdir_p!(proj_out)

    previous = Application.get_env(:cure, :stdlib_beam_dir)
    Application.put_env(:cure, :stdlib_beam_dir, beam_dir)

    on_exit(fn ->
      case previous do
        nil -> Application.delete_env(:cure, :stdlib_beam_dir)
        value -> Application.put_env(:cure, :stdlib_beam_dir, value)
      end

      File.rm_rf!(beam_dir)
      File.rm_rf!(source_dir)
      File.rm_rf!(proj_out)
    end)

    source = Path.join(source_dir, "fake.cure")
    File.write!(source, "mod Std.Fake\n  fn value() -> Int = 1\n")

    assert {:ok, %{errors: []}} =
             canonical_sweep([source], beam_dir,
               source_roots: [source_dir],
               artifact_kind: :stdlib
             )

    h1 = Artifacts.stdlib_fingerprint()

    File.write!(source, "mod Std.Fake\n  fn value() -> Int = 2\n")

    assert {:ok, %{errors: []}} =
             canonical_sweep([source], beam_dir,
               source_roots: [source_dir],
               artifact_kind: :stdlib
             )

    h2 = Artifacts.stdlib_fingerprint()
    assert h1 != h2

    # ...and it is genuinely reading the beam dir, not the empty project dir
    # (whose output-scoped fingerprint is the constant the old caller used).
    assert h2 != Artifacts.stdlib_fingerprint(proj_out)
  end

  # LIMITATION 2 (a stale `@prelude` manifest survives across same-process
  # builds). `Cure.Elab.Program.prelude_manifest/0` memoizes the set of
  # `@prelude`-marked stdlib items in `:persistent_term`, keyed by the source
  # dir, assuming the stdlib is immutable for the process lifetime — the same
  # assumption incremental compilation of the stdlib violates. Without eviction,
  # a second same-process build sees the FIRST build's ambient-prelude set even
  # after a marker changed on disk, so a module can be elaborated against a wrong
  # ambient scope. Fixture pattern mirrors the stale-interface test above.
  test "an incremental rebuild refreshes the @prelude manifest when a stdlib source's markers change",
       %{out: out} do
    stdlib_src =
      Path.join(System.tmp_dir!(), "cure_prelude_cache_#{:erlang.unique_integer([:positive])}")

    File.mkdir_p!(stdlib_src)
    previous = Application.get_env(:cure, :stdlib_source_dir)
    Application.put_env(:cure, :stdlib_source_dir, stdlib_src)

    on_exit(fn ->
      case previous do
        nil -> Application.delete_env(:cure, :stdlib_source_dir)
        value -> Application.put_env(:cure, :stdlib_source_dir, value)
      end

      Cure.Elab.Program.invalidate_prelude_manifest()
      File.rm_rf!(stdlib_src)
    end)

    p_path = Path.join(stdlib_src, "p.cure")
    q_path = Path.join(stdlib_src, "q.cure")
    # P marks a type ambient via `@prelude`; Q is a bystander so the walk has >1
    # module and the manifest is genuinely consulted during elaboration.
    File.write!(p_path, "mod P\n  @prelude typealias Widget = Int\n  fn p() -> Int = 1\n")
    File.write!(q_path, "mod Q\n  fn q() -> Int = 2\n")
    paths = Path.wildcard(Path.join(stdlib_src, "*.cure"))

    assert {:ok, _s1} = canonical_sweep(paths, out, source_roots: [stdlib_src])
    # Build 1 populates the per-dir manifest cache: P contributes a prelude mark.
    assert Enum.any?(Cure.Elab.Program.prelude_manifest(), &(&1.source == "P")),
           "build 1 should have recorded P as a @prelude provider"

    # Remove the marker and rebuild in the SAME process.
    File.write!(p_path, "mod P\n  typealias Widget = Int\n  fn p() -> Int = 1\n")
    assert {:ok, s2} = canonical_sweep(paths, out, source_roots: [stdlib_src])
    assert "P" in compiled(s2)

    refute Enum.any?(Cure.Elab.Program.prelude_manifest(), &(&1.source == "P")),
           "stale @prelude manifest: P still marked after its marker was removed and it recompiled"
  end

  # Regression (cold-clone bootstrap): a `@prelude` provider under `Std.*` is
  # injected as an ambient `use` into EVERY sibling module (`inject_prelude_uses/2`),
  # `compile_order/1` now follows the canonical dependency graph, including ambient
  # prelude providers. The provider must therefore precede its consumer even when
  # filenames sort in the opposite order, and a cold build must succeed without any
  # pre-existing BEAM artifact.
  @std_ambient_provider """
  @prelude
  mod Std.AmbientFixture
    fn ambient() -> Int = 7
  """

  @std_ambient_consumer """
  mod Std.AlphaFixture
    fn alpha() -> Int = 1
  """

  test "an injected ambient @prelude provider is ordered and compiles from a cold bootstrap" do
    root = Path.join(System.tmp_dir!(), "cure_cold_#{:erlang.unique_integer([:positive])}")
    src = Path.join(root, "std")
    out = Path.join(root, "ebin")
    File.mkdir_p!(src)
    on_exit(fn -> File.rm_rf!(root) end)

    File.write!(Path.join(src, "ambient_fixture.cure"), @std_ambient_provider)
    File.write!(Path.join(src, "alpha_fixture.cure"), @std_ambient_consumer)
    paths = Path.wildcard(Path.join(src, "*.cure"))

    prior = Application.get_env(:cure, :stdlib_source_dir)
    Application.put_env(:cure, :stdlib_source_dir, src)

    on_exit(fn ->
      if prior,
        do: Application.put_env(:cure, :stdlib_source_dir, prior),
        else: Application.delete_env(:cure, :stdlib_source_dir)
    end)

    {:ok, graph} = DepGraph.scan(paths)
    pos = compile_order(graph) |> Enum.with_index() |> Map.new()

    assert pos["Std.AmbientFixture"] < pos["Std.AlphaFixture"],
           "the canonical dependency graph must schedule the ambient provider first"

    assert {:ok, s} = canonical_sweep(paths, out, source_roots: [src])

    assert s.errors == [],
           "cold build must not require a prebuilt beam for an injected @prelude import"

    assert compiled(s) == ["Std.AlphaFixture", "Std.AmbientFixture"]
  end

  defp semantic_set(set) do
    Map.new(set.modules, fn {name, entry} ->
      artifacts =
        entry.artifacts
        |> Enum.map(&{&1.module, &1.exports_hash})
        |> Enum.sort()

      {name, %{interface_hash: entry.interface_hash, edges: entry.edges, artifacts: artifacts}}
    end)
  end
end
