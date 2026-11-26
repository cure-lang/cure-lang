defmodule Cure.Compiler.BufferGrammarTest do
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.{Program, SourceContext}
  alias Cure.LSP.Server

  @moduletag :tmp_dir

  defp providers(root) do
    File.write!(Path.join(root, "unrelated-one.cure"), "mod Main\n  fn unrelated() -> Int = 1\nend\n")
    File.write!(Path.join(root, "unrelated-two.cure"), "mod Main\n  fn unrelated() -> Int = 2\nend\n")

    File.write!(Path.join(root, "arbitrary-helper-filename.cure"), """
    mod Buffer.Helper
      macro Rules
        tactic private_finish <e: Code> becomes exact e
    end
    """)

    provider = Path.join(root, "not-a-module-name.cure")

    File.write!(provider, """
    mod Buffer.Provider
      use Buffer.Helper
      use Std.Tactic
      use Std.Syntax
      macro Rules
        tactic finish <e: Code> becomes private_finish e
        tactic computed_finish computed by close_goal
      fn close_goal(g: Goal) -> MacroResult = expand(Std.Tactic.simplify(g))
      fn own_proof(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because private_finish reflexive(x)
    end
    """)

    provider
  end

  test "grouped standard imports name their modules, not a phantom Std provider" do
    source = """
    mod GroupedStandardBuffer
      use Std.{Equivalent, List, Core, Math}
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because simplify
    end
    """

    facts =
      Cure.Compiler.Parser.FixityScan.harvest_source(
        source,
        "grouped-std.cure",
        Cure.Compiler.Parser.BuiltinFixity.table()
      )

    assert Enum.map(facts.uses, & &1.target) == ["Std.Equivalent", "Std.List", "Std.Core", "Std.Math"]
    assert {:ok, env} = Cure.Compiler.check_source(source)
    assert :ok = Kernel.check_def(env, :"GroupedStandardBuffer#theorem")
    assert {:ok, :"Cure.GroupedStandardBuffer"} = Cure.Compiler.compile_and_load(source)
  end

  test "grouped user imports share header and semantic resolution without a namespace module", %{tmp_dir: root} do
    providers(root)

    source =
      consumer("finish reflexive(x)", "Buffer.GroupedConsumer")
      |> String.replace("use Buffer.Provider", "use Buffer.{Provider, Helper}")

    opts = [file: Path.join(root, "grouped.cure"), source_roots: [root]]
    assert {:ok, env} = Cure.Compiler.check_source(source, opts)
    assert :ok = Kernel.check_def(env, :"Buffer.GroupedConsumer#theorem")
    assert {:ok, :"Cure.Buffer.GroupedConsumer"} = Cure.Compiler.compile_and_load(source, opts)
  end

  defp consumer(command, module \\ "Buffer.Consumer") do
    """
    mod #{module}
      use Buffer.Provider
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because #{command}
    end
    """
  end

  test "all single-buffer routes share imported template and computed grammars", %{tmp_dir: root} do
    providers(root)

    for {command, name} <- [{"finish reflexive(x)", "Template"}, {"computed_finish", "Computed"}] do
      source = consumer(command, "Buffer." <> name)
      path = Path.join(root, "absent-#{name}.cure")
      opts = [file: path, source_roots: [root]]
      refute File.exists?(path)
      assert {:ok, env} = Cure.Compiler.check_source(source, opts)
      definition = String.to_atom("Buffer.#{name}#theorem")
      assert :ok = Kernel.check_def(env, definition)
      assert Env.total?(env, definition)
      assert {:ok, plain} = Program.elaborate(source, opts)
      assert Env.get_def(plain, definition).body == Env.get_def(env, definition).body
      assert {:ok, loaded} = Cure.Compiler.compile_and_load(source, opts)
      assert loaded == String.to_atom("Cure.Buffer.#{name}")

      assert {:ok, _module, _warnings} =
               Cure.Compiler.compile_string(
                 source,
                 opts ++ [output_dir: Path.join(root, "ebin-#{name}"), emit_events: false]
               )

      refute File.exists?(path)
    end
  end

  test "active text overrides disk and preserves exact authored source identities", %{tmp_dir: root} do
    providers(root)
    path = Path.join(root, "consumer.cure")
    File.write!(path, "not the active program")
    source = consumer("finish reflexive(x)")
    assert {{:ok, _}, context} = SourceContext.analyze(source, file: path, source_roots: [root])
    assert [%{goal: "Equivalent(Int, x, x)"}] = SourceContext.at(context, position(source, "finish"))
    assert [] = SourceContext.at(context, position(source, "finish reflexive(x)", :end))
    assert File.read!(path) == "not the active program"

    for file <- ["nofile", "relative-buffer.cure"] do
      assert {{:ok, _}, context} = SourceContext.analyze(source, file: file, source_roots: [root])
      assert [_ | _] = context.observations
      assert Enum.all?(context.observations, &(&1.scope.source_id == file))
    end
  end

  test "unknown providers and requested duplicate identities fail without guessing", %{tmp_dir: root} do
    providers(root)
    source = consumer("finish reflexive(x)")
    opts = [file: Path.join(root, "virtual.cure"), source_roots: [root]]
    missing_source = String.replace(source, "Buffer.Provider", "Absent.Provider")
    assert {:error, missing} = Cure.Compiler.check_source(missing_source, opts)
    {missing_diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic(missing, opts[:file], missing_source)
    assert missing_diagnostic.code == "E091"
    File.write!(Path.join(root, "duplicate.cure"), "mod Buffer.Provider\nend\n")

    assert {:error, {:parse_error, {:duplicate_module_identity, "Buffer.Provider", [_, _]}} = duplicate} =
             Cure.Compiler.check_source(source, opts)

    {duplicate_diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic(duplicate, opts[:file], source)
    refute duplicate_diagnostic.code == "E101"
  end

  test "ordinary parse errors and local macro Core remain compatible", %{tmp_dir: root} do
    providers(root)
    opts = [file: Path.join(root, "bad.cure"), source_roots: [root]]
    source = consumer("finish (")
    assert {:error, {:parse_error, errors}} = Cure.Compiler.check_source(source, opts)
    assert is_list(errors)

    local = """
    mod LocalGrammarParity
      macro Rules
        tactic local_finish <e: Code> becomes exact e
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because local_finish reflexive(x)
    end
    """

    assert {:ok, env} = Cure.Compiler.check_source(local)
    assert {:ok, plain} = Cure.Compiler.check_source(String.replace(local, "because local_finish", "because exact"))

    assert Env.get_def(env, :"LocalGrammarParity#theorem").body ==
             Env.get_def(plain, :"LocalGrammarParity#theorem").body
  end

  test "imported tactics cannot admit partial false proofs", %{tmp_dir: root} do
    providers(root)

    source = """
    mod Buffer.False
      use Buffer.Provider
      use Std.Nat
      fn loop() -> Equivalent(Nat, Z(), S(Z())) = loop()
      fn theorem() -> Equivalent(Nat, Z(), S(Z())) = proof chain
        Z() == S(Z())
        because finish loop()
    end
    """

    opts = [file: Path.join(root, "false.cure"), source_roots: [root]]

    for result <- [Cure.Compiler.check_source(source, opts), Cure.Compiler.compile_and_load(source, opts)] do
      assert {:error, reason} = result
      {diagnostic, _} = Cure.Compiler.Errors.to_diagnostic(reason, opts[:file], source)
      assert diagnostic.code == "E013"
    end
  end

  test "real LSP analyzes the unsaved imported-tactic document and invalidates dependent cache", %{tmp_dir: root} do
    providers(root)
    path = Path.join(root, "consumer.cure")
    File.write!(path, "old disk contents")
    uri = "file://" <> path
    source = consumer("finish reflexive(x)")

    {state, _} =
      rpc("textDocument/didOpen", %{"textDocument" => %{"uri" => uri, "text" => source, "version" => 1}}, %Server{})

    params = %{"textDocument" => %{"uri" => uri}, "version" => 1, "position" => position(source, "finish")}
    {state, %{"result" => %{"goals" => [%{"goal" => "Equivalent(Int, x, x)"}]}}} = rpc("cure/proofState", params, state)

    {state, %{"result" => %{"goals" => []}}} =
      rpc("cure/proofState", %{params | "position" => position(source, "finish reflexive(x)", :end)}, state)

    provider_uri = "file://" <> Path.join(root, "not-a-module-name.cure")

    {state, _} =
      rpc(
        "textDocument/didOpen",
        %{
          "textDocument" => %{
            "uri" => provider_uri,
            "text" => File.read!(Path.join(root, "not-a-module-name.cure")),
            "version" => 1
          }
        },
        state
      )

    refute Map.has_key?(state.ast_cache, uri)
    {state, _} = rpc("textDocument/didClose", %{"textDocument" => %{"uri" => provider_uri}}, state)
    assert state.ast_cache == %{}
    assert File.read!(path) == "old disk contents"
  end

  test "saved provider changes refresh unchanged consumer versions after didSave", %{tmp_dir: root} do
    provider = providers(root)
    path = Path.join(root, "consumer.cure")
    source = consumer("finish reflexive(x)")
    uri = "file://" <> path
    provider_uri = "file://" <> provider

    {state, _} =
      rpc("textDocument/didOpen", %{"textDocument" => %{"uri" => uri, "text" => source, "version" => 1}}, %Server{})

    endpoint = %{
      "textDocument" => %{"uri" => uri},
      "version" => 1,
      "position" => position(source, "finish reflexive(x)", :end)
    }

    {state, %{"result" => %{"goals" => []}}} = rpc("cure/proofState", endpoint, state)

    edited =
      String.replace(
        File.read!(provider),
        "tactic finish <e: Code> becomes private_finish e",
        "tactic finish <e: Code> becomes exact missing_saved_proof"
      )

    {state, _} =
      rpc(
        "textDocument/didOpen",
        %{"textDocument" => %{"uri" => provider_uri, "text" => File.read!(provider), "version" => 1}},
        state
      )

    {state, _} =
      rpc(
        "textDocument/didChange",
        %{"textDocument" => %{"uri" => provider_uri, "version" => 2}, "contentChanges" => [%{"text" => edited}]},
        state
      )

    # Unsaved sibling overlays are deliberately not the semantic provider input.
    {state, %{"result" => %{"goals" => []}}} = rpc("cure/proofState", endpoint, state)
    File.write!(provider, edited)
    {state, _} = rpc("textDocument/didSave", %{"textDocument" => %{"uri" => provider_uri}}, state)
    assert state.ast_cache == %{}

    {_state, %{"result" => %{"version" => 1, "goals" => [%{"goal" => "Equivalent(Int, x, x)"}]}}} =
      rpc("cure/proofState", endpoint, state)
  end

  test "changed saved computed providers do not reuse a global macro-home environment", %{tmp_dir: root} do
    provider = providers(root)
    source = consumer("computed_finish")
    opts = [file: Path.join(root, "virtual.cure"), source_roots: [root]]
    assert {:ok, _} = Cure.Compiler.check_source(source, opts)

    File.write!(
      provider,
      String.replace(File.read!(provider), "expand(Std.Tactic.simplify(g))", ~s|reject_goal("saved callback changed")|)
    )

    assert {:error, _} = Cure.Compiler.check_source(source, opts)
  end

  test "cyclic provider imports terminate and local rules retain canonical shadowing", %{tmp_dir: root} do
    File.write!(Path.join(root, "a.cure"), """
    mod Cycle.A
      use Cycle.B
      macro Rules
        tactic finish becomes simplify
    end
    """)

    File.write!(Path.join(root, "b.cure"), "mod Cycle.B\n  use Cycle.A\nend\n")

    source = """
    mod Cycle.Consumer
      use Cycle.A
      macro Rules
        tactic finish becomes exact missing_local_wins
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because finish
    end
    """

    opts = [file: Path.join(root, "virtual.cure"), source_roots: [root]]
    assert {:error, _} = Cure.Compiler.check_source(source, opts)
    assert {:ok, env} = Cure.Compiler.check_source(String.replace(source, "exact missing_local_wins", "simplify"), opts)
    assert :ok = Kernel.check_def(env, :"Cycle.Consumer#theorem")
  end

  test "supplied canonical providers outside empty source roots survive nested callback loading", %{tmp_dir: root} do
    provider = providers(root)
    helper = Path.join(root, "arbitrary-helper-filename.cure")
    assert {:ok, index} = Cure.Compiler.ModuleIndex.build([provider, helper], validate_dependencies: false)

    for command <- ["finish reflexive(x)", "computed_finish"] do
      source = consumer(command, "Buffer.IndexedConsumer")
      opts = [file: Path.join(root, "virtual/consumer.cure"), source_roots: [], module_index: index]
      assert {:ok, env} = Cure.Compiler.check_source(source, opts)
      assert :ok = Kernel.check_def(env, :"Buffer.IndexedConsumer#theorem")
      assert {:ok, :"Cure.Buffer.IndexedConsumer"} = Cure.Compiler.compile_and_load(source, opts)
    end
  end

  defp rpc(method, params, state) do
    key = make_ref()

    output =
      capture_io(fn ->
        {next, _} = Server.process_message(%{"id" => 42, "method" => method, "params" => params}, state)
        Process.put(key, next)
      end)

    {responses, ""} = Cure.LSP.Transport.parse_buffer(output)
    {Process.delete(key), List.first(responses)}
  end

  defp position(source, needle, endpoint \\ :start) do
    {byte, size} = :binary.match(source, needle)
    prefix = binary_part(source, 0, byte + if(endpoint == :end, do: size, else: 0))
    lines = String.split(prefix, "\n")
    %{"line" => length(lines) - 1, "character" => String.length(List.last(lines))}
  end
end
