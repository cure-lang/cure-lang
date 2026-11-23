defmodule Cure.Elab.SourceContextTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Cure.Core.Kernel
  alias Cure.Elab.{Emit, Program, ProofState, SourceContext}
  alias Cure.LSP.Server
  alias Cure.Pipeline.Events

  @source """
  mod SourceGoals
    fn convert(input: Int) -> Float = 1.0
    fn pair(left: Int, right: Int) -> Int = left
    fn nested(x: Int) -> Float = convert(?argument)
    fn repeated(x: Int) -> Int = pair(?same, ?same)
    fn other() -> Float = ?second
    fn text() -> String = "?phantom"
    # ?comment is not a hole
  end
  """

  test "canonical checks expose nested targets, occurrence indices and authored names" do
    assert {{:ok, env}, context} = SourceContext.analyze(@source, file: "goals.cure", version: 7)
    assert context.file == "goals.cure"
    assert context.text == @source
    assert context.hash == :crypto.hash(:sha256, @source)
    assert context.version == 7
    assert [nested, first, second, other] = Program.hole_goals(env, context)
    assert nested.goal == "Int"
    assert nested.context == ["x : Int"]
    assert first.id == second.id
    assert first.span != second.span
    assert Enum.map([nested, first, second, other], & &1.occurrence_index) == [0, 1, 2, 3]
    assert other.goal == "Float"
    assert [_, _, _] = SourceContext.remaining(context)
    assert :ok = Kernel.check_def(env, :"SourceGoals#convert")
    assert :ok = Kernel.check_def(env, :"SourceGoals#text")

    assert {:error, {:unfilled_hole, _}} =
             Emit.compile_forms(env, :SourceGoals, Map.keys(Program.program_owned_definitions(env)))
  end

  test "separate sources with identical logical IDs never share targets or names" do
    source_a = "mod Isolated\n  fn later(alpha: Int) -> Int = ?same\nend\n"
    source_b = "mod Isolated\n  fn later(beta: Float) -> Float = ?same\nend\n"
    assert {{:ok, _}, a} = SourceContext.analyze(source_a, file: "a.cure")
    assert {{:ok, _}, b} = SourceContext.analyze(source_b, file: "b.cure")
    assert [%{id: id, goal: "Int", context: ["alpha : Int"]}] = SourceContext.hole_goals(a)
    assert [%{id: ^id, goal: "Float", context: ["beta : Float"]}] = SourceContext.hole_goals(b)
    assert [%{goal: "Int"}] = SourceContext.hole_goals(a)
    refute a.hash == b.hash
  end

  test "dependent hypotheses retain source binder names" do
    source = """
    mod DependentGoals
      use Std.Equivalent
      fn later(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Int, y, x) = ?proof
    end
    """

    assert {{:ok, _}, context} = SourceContext.analyze(source)
    assert [%{goal: "Equivalent(Int, y, x)", context: names}] = SourceContext.hole_goals(context)
    assert "h : Equivalent(Int, x, y)" in names
    assert "x : Int" in names
    assert "y : Int" in names
  end

  test "imported holes are excluded even when their logical names match" do
    root = Path.join(System.tmp_dir!(), "cure-source-context-#{System.unique_integer([:positive])}")
    File.mkdir_p!(root)
    on_exit(fn -> File.rm_rf!(root) end)
    File.write!(Path.join(root, "imported.cure"), "mod Imported\n  fn pending() -> Int = ?same\nend\n")
    source = "mod LocalGoals\n  use Imported\n  fn later() -> Float = ?same\nend\n"

    assert {{:ok, env}, context} =
             SourceContext.analyze(source, file: Path.join(root, "local.cure"), source_roots: [root])

    assert [%{function: :"LocalGoals#later", goal: "Float"}] = Program.hole_goals(env, context)
  end

  test "hints use individual checked goals and ignore string/comment phantoms" do
    hints = Server.compute_inlay_hints(@source) |> Enum.filter(&String.starts_with?(&1["label"], "?"))
    assert [nested, first, second, other] = hints
    assert nested["label"] == "? Int  (context: x : Int)"
    assert first["label"] == second["label"]
    assert other["label"] == "? Float"
    refute first["position"] == second["position"]
  end

  test "refused canonical checks retain partial observations and honest lexical fallback" do
    source = "mod FailedGoals\n  fn later() -> Int = ?observed\n  fn broken() -> Int = missing(?unreached)\nend\n"
    assert {{:error, _}, context} = SourceContext.analyze(source)
    assert [%{goal: "Int"}] = SourceContext.hole_goals(context)
    hints = Server.compute_inlay_hints(context, :utf16)
    assert Enum.any?(hints, &(&1["label"] == "? goal unavailable"))
    refute Enum.any?(hints, &(&1["label"] =~ "? Float"))

    # A parse failure still permits genuine lexer tokens, never regex matches.
    parse_error = "mod Broken\n  fn f() -> Int = ?real +\n  # ?not_real\n"
    assert {{:error, _}, failed} = SourceContext.analyze(parse_error)

    assert [%{"label" => "? goal unavailable"}] =
             Server.compute_inlay_hints(failed, :utf16) |> Enum.filter(&String.starts_with?(&1["label"], "?"))
  end

  test "CRLF and multibyte hole positions follow the negotiated encoding" do
    source = "mod UnicodeGoals\r\n  fn later() -> Int = let marker = \"é𐐀\"; ?actual\r\nend\r\n"
    # Use a valid multiline body while retaining Unicode before the same-line hole.
    source = String.replace(source, "let marker = \"é𐐀\"; ?actual", "pair(\"é𐐀\", ?actual)")
    source = String.replace(source, "  fn later", "  fn pair(marker: String, value: Int) -> Int = value\r\n  fn later")
    assert {{:ok, _}, context} = SourceContext.analyze(source)

    for {encoding, difference} <- [utf8: 0, utf16: 3, utf32: 4] do
      [hint] = Server.compute_inlay_hints(context, encoding) |> Enum.filter(&String.starts_with?(&1["label"], "?"))
      [_, _, line | _] = String.split(source, "\r\n")
      {byte, _} = :binary.match(line, "?actual")
      assert hint["position"] == %{"line" => 2, "character" => byte - difference}
    end
  end

  test "LSP shares one canonical analysis per version and refuses stale or closed requests" do
    Events.subscribe(:type_checker, :proof_state)
    uri = "file:///source-context.cure"

    {state, _} =
      rpc("textDocument/didOpen", %{"textDocument" => %{"uri" => uri, "text" => @source, "version" => 1}}, %Server{})

    context = state.ast_cache[uri].analysis |> elem(1)
    drain_events()
    params = %{"textDocument" => %{"uri" => uri}, "version" => 1}
    {after_request, %{"result" => %{"version" => 1, "goals" => [_, _, _]}}} = rpc("cure/proofState", params, state)
    assert context == elem(after_request.ast_cache[uri].analysis, 1)
    {_state, _} = rpc("textDocument/inlayHint", params, after_request)
    refute_receive {Events, :type_checker, :proof_state, _, _}
    {_state, %{"error" => %{"code" => -32801}}} = rpc("cure/proofState", %{params | "version" => 0}, after_request)
    replacement = String.replace(@source, "?second", "1.0")

    {changed, _} =
      rpc(
        "textDocument/didChange",
        %{"textDocument" => %{"uri" => uri, "version" => 2}, "contentChanges" => [%{"text" => replacement}]},
        after_request
      )

    refute elem(changed.ast_cache[uri].analysis, 1).hash == context.hash
    {closed, _} = rpc("textDocument/didClose", %{"textDocument" => %{"uri" => uri}}, changed)
    refute Map.has_key?(closed.ast_cache, uri)
    refute Map.has_key?(closed.document_versions, uri)
    {_state, %{"error" => %{"code" => -32801}}} = rpc("cure/proofState", params, closed)
  end

  test "authoritative session snapshots replace nested stale command frontiers" do
    assert {{:ok, _}, context} = SourceContext.analyze(@source)
    [hole | _] = context.observations
    [view] = hole.goals
    child = %{hole | kind: :command, id: :child, goals: [%{view | id: "p"}]}
    session = %{hole | kind: :session, id: {:session, :root}, goals: [%{view | id: "p"}, %{view | id: "q"}]}
    assert [%{id: "p"}, %{id: "q"}] = ProofState.remaining([child, session])
    assert [] = ProofState.remaining([child, session, %{session | goals: []}])
  end

  test "overload observations and subscribed events belong only to the unique winning candidate" do
    Events.subscribe(:type_checker, :proof_state)
    int = "  fn choose(value: Int, tag: Int) -> Int = value\n"
    float = "  fn choose(value: Float, tag: String) -> Float = value\n"

    for declarations <- [int <> float, float <> int],
        {tag, expected} <- [{~s("selected"), "Float"}, {"3", "Int"}] do
      source =
        "mod OverloadedGoals\n" <>
          declarations <>
          "  fn later() -> #{expected} = choose(?actual, #{tag})\nend\n"

      assert {{:ok, env}, context} = SourceContext.analyze(source)
      assert [%{goal: ^expected}] = SourceContext.hole_goals(context)
      assert :ok = Kernel.check_def(env, :"OverloadedGoals#later")
      assert_receive {Events, :type_checker, :proof_state, %{kind: :hole, goals: [%{goal: ^expected}]}, _}
      refute_receive {Events, :type_checker, :proof_state, _, _}
    end

    source =
      "mod OverloadedGoals\n" <>
        int <>
        float <>
        "  fn later() -> Int = choose(?actual, ?tag)\nend\n"

    assert {{:error, _}, context} = SourceContext.analyze(source)
    assert [] = SourceContext.hole_goals(context)
    refute_receive {Events, :type_checker, :proof_state, _, _}

    assert [%{"label" => "? goal unavailable"}, %{"label" => "? goal unavailable"}] =
             Server.compute_inlay_hints(context, :utf16)
             |> Enum.filter(&String.starts_with?(&1["label"], "?"))
  end

  @tag :tmp_dir
  test "CLI check and REPL hole surfaces show the nested argument target", %{tmp_dir: root} do
    source = """
    mod CommandGoals
      fn convert(input: Int) -> Float = 1.0
      fn later(x: Int) -> Float = convert(?argument)
    end
    """

    path = Path.join(root, "goals.cure")
    File.write!(path, source)

    warning =
      capture_io(:stderr, fn ->
        capture_io(fn -> Cure.CLI.main(["check", path]) end)
      end)

    assert warning =~ "Goal: Int"
    assert warning =~ "Context: x : Int"
    refute warning =~ "Goal: Float"

    declarations = "fn convert(input: Int) -> Float = 1.0\nfn later(x: Int) -> Float = convert(?argument)"
    assert {:definitions, entries} = Cure.REPL.Session.classify(declarations)
    assert {:ok, [%{goal: "Int", context: ["x : Int"]}]} = Cure.REPL.Session.hole_goals(entries)

    output =
      capture_io(fn ->
        state = Cure.REPL.__new_state__(error_device: :stdio)
        state = Cure.REPL.__submit__(state, declarations)
        state = Cure.REPL.__submit__(state, ";;")
        Cure.REPL.__submit__(state, ":holes")
      end)

    assert output =~ "later : Int (context: x : Int)"
    refute output =~ "later : Float"
  end

  defp rpc(method, params, state) do
    key = make_ref()

    output =
      capture_io(fn ->
        {next, _} = Server.process_message(%{"id" => 42, "method" => method, "params" => params}, state)
        Process.put(key, next)
      end)

    {[response], ""} = Cure.LSP.Transport.parse_buffer(output)
    {Process.delete(key), response}
  end

  defp drain_events do
    receive do
      {Events, :type_checker, :proof_state, _, _} -> drain_events()
    after
      0 -> :ok
    end
  end
end
