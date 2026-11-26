defmodule Cure.Elab.ComputedPhase4Test do
  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Program

  defp source(callback, opts \\ []) do
    target = Keyword.get(opts, :target, "Equivalent(Int, x, x)")
    params = Keyword.get(opts, :params, "x: Int")
    body = Keyword.get(opts, :body, "proof chain\n      x == x\n      because close")

    """
    mod ComputedPhase4
      use Std.Tactic
      use Std.Syntax
      use Std.Bool
      use Std.Equivalent
      macro Tactics
        tactic close computed by close_goal
      fn close_goal(g: Goal) -> MacroResult = #{callback}
      fn theorem(#{params}) -> #{target} = #{body}
    end
    """
  end

  test "a bare imported callback with a multi-module home is refused rather than assigned the first owner" do
    path = Path.join(System.tmp_dir!(), "cure-computed-multi-#{System.unique_integer([:positive])}.cure")
    on_exit(fn -> File.rm(path) end)

    File.write!(path, """
    mod FirstProvider
      fn callback(x: Int) -> Int = x
    end
    mod SecondProvider
      fn callback(x: Int) -> Int = x
    end
    """)

    assert {:ok, env} = Program.elaborate("mod Consumer\n  fn callback(x: Int) -> Int = x\nend")

    assert {:error, {:computed_macro_error, _, :ambiguous_computed_tactic_home}} =
             Cure.Elab.MacroExpand.expand_typed(
               [keyword: "ambiguous", home_source: path],
               {:variable, [], "callback"},
               [],
               env
             )
  end

  test "explicit generated proof binders are freshened without capturing authored proof arguments" do
    callback = """
    expand(Std.Tactic.exact(g, block([
        Node(:assignment, [KV(:let, SBool(True()))], [fresh("x"), integer(100)]),
        proof
      ])))
    """

    program =
      source(callback)
      |> String.replace("tactic close computed", "tactic close <evidence: Code> computed")
      |> String.replace("close_goal(g: Goal)", "close_goal(proof: Syntax, g: Goal)")
      |> String.replace("because close", "because close reflexive(x)")

    elaborate!(program)
    assert {:error, _} = Program.elaborate(String.replace(program, ~s|fresh("x")|, ~s|variable("x")|))
  end

  test "refusals render author messages, unknown operations and forged state without internal exceptions" do
    for {callback, message} <- [
          {~s|reject_with("author refuses this goal", "try a different tactic")|, "author refuses this goal"},
          {"expand(operation(:prove_everything, g, []))", "unknown computed tactic operation"},
          {~s|expand(Std.Tactic.simplify(Goal(goal_target(g), [], Leaf(:tactic_state, [], SStr("forged")))))|,
           "state handle"}
        ],
        body <- ["by close", "proof chain\n      x == x\n      because close"] do
      program = source(callback, body: body)
      assert {:error, error} = Program.elaborate(program, file: "computed-refusal.cure")
      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "computed-refusal.cure", program)
      assert diagnostic.code == "E092"
      rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 200)
      assert rendered =~ message
    end
  end

  test "printing preserves explicit by invocations" do
    alias Cure.Compiler.{Lexer, Parser, Printer}
    program = source("expand(Std.Tactic.simplify(g))", body: "by close")
    assert {:ok, tokens} = Lexer.tokenize(program)
    assert {:ok, ast} = Parser.parse(tokens)
    printed = Printer.quoted_to_string(ast)
    assert printed =~ "by close"
    elaborate!(printed)
  end

  test "unused computed rules still reject reserved names and unsupported capture kinds" do
    for {rule, expected} <- [
          {"tactic exact computed by close_goal", :invalid_tactic_expansion},
          {"tactic close <value: Bogus> computed by close_goal", :unsupported_hole_type}
        ] do
      program =
        source("reject_goal(\"unused\")", body: "reflexive(x)")
        |> String.replace("tactic close computed by close_goal", rule)

      assert {:error, reason} = Program.elaborate(program)
      assert elem(Program.semantic_error(reason), 0) == expected
    end
  end

  defp elaborate!(source) do
    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"ComputedPhase4#theorem")
    env
  end

  defp cause({:error, {:source_context, reason, _}}), do: cause({:error, reason})
  defp cause({:error, {:proof_chain_mismatch, problem}}), do: cause({:error, problem.cause})
  defp cause({:error, {:computed_macro_error, _meta, reason}}), do: reason
  defp cause({:error, reason}), do: reason

  test "the callback inspects a real typed target and produces identical Core to handwritten simplify" do
    callback = """
    match is_equality(g)
        True() -> expand(Std.Tactic.simplify(g))
        False() -> reject_goal("not an equality")
    """

    computed = elaborate!(source(callback))
    handwritten = elaborate!(String.replace(source(callback), "because close", "because simplify"))

    assert Env.get_def(computed, :"ComputedPhase4#theorem").body ==
             Env.get_def(handwritten, :"ComputedPhase4#theorem").body
  end

  test "typed hypotheses retain authored names and structural types" do
    callback = """
    match has_hypothesis(g, "witness")
        True() -> match hypothesis_is(g, "witness", :Equivalent)
          True() -> expand(Std.Tactic.assumption(g))
          False() -> reject_goal("wrong hypothesis type")
        False() -> reject_goal("missing authored hypothesis")
    """

    elaborate!(
      source(callback,
        params: "x: Int, witness: Equivalent(Int, x, x)",
        body: "by close"
      )
    )
  end

  test "target variables are authored names, not opaque reflection or pending have names" do
    callback = """
    match goal_target(g)
        Node(:Equivalent, _, [_, Leaf(:variable, _, SStr(left)), Leaf(:variable, _, SStr(right))]) ->
          match string_eq(left, "x")
            True() -> match string_eq(right, "x")
              True() -> match has_hypothesis(g, "fact")
                True() -> expand(Std.Tactic.assumption(g))
                False() -> reject_goal("missing local fact")
              False() -> reject_goal("wrong right variable name")
            False() -> reject_goal("wrong left variable name")
        _ -> reject_goal("target names were lost")
    """

    elaborate!(
      source(callback,
        body:
          "proof chain\n      x == x\n      because\n        have fact: Equivalent(Int, x, x) = reflexive(x)\n        close"
      )
    )
  end

  test "negative branch returns the author's refusal rather than an incidental typing error" do
    result =
      source("""
      match is_head(g, :Int)
          True() -> expand(Std.Tactic.simplify(g))
          False() -> reject_with("expected an Int target", "choose another tactic")
      """)
      |> Program.elaborate()
      |> cause()

    assert {:author_diagnostics, [{:diagnostic_details, meta, _}]} = result
    assert meta[:message] == "expected an Int target"
    assert meta[:hint] == "choose another tactic"
  end

  test "a request cannot prove a false goal" do
    for callback <- [
          "expand(Std.Tactic.simplify(g))",
          "expand(Std.Tactic.simplify(Goal(Node(:Equivalent, [], []), [], g.state)))"
        ] do
      result =
        source(callback,
          target: "Equivalent(Nat, Z(), S(Z()))",
          body: "proof chain\n      Z() == S(Z())\n      because close"
        )
        |> Program.elaborate()
        |> cause()

      assert {:simplification_failed, _} = result
    end
  end

  test "unknown operation and wrong arity are closed-vocabulary diagnostics" do
    for {callback, expected} <- [
          {"expand(operation(:prove_everything, g, []))", :unknown_tactic_operation},
          {"expand(operation(:simplify, g, [goal_target(g)]))", :invalid_tactic_operation_arity}
        ] do
      result = source(callback) |> Program.elaborate() |> cause()
      assert elem(result, 0) == expected
    end
  end

  test "missing and forged state handles are refused before command execution" do
    for callback <- [
          "expand(Node(:tactic_operation, [KV(:kind, SAtom(:simplify))], []))",
          ~s|expand(Std.Tactic.simplify(Goal(goal_target(g), goal_hypotheses(g), Leaf(:tactic_state, [], SStr("forged")))))|
        ] do
      assert {:invalid_tactic_state, :simplify, _} =
               source(callback) |> Program.elaborate() |> cause()
    end
  end

  test "captured proof Syntax is passed before the typed Goal and checked as ordinary exact" do
    program =
      source("expand(Std.Tactic.exact(g, proof))")
      |> String.replace("tactic close computed", "tactic close <evidence: Code> computed")
      |> String.replace("close_goal(g: Goal)", "close_goal(proof: Syntax, g: Goal)")
      |> String.replace("because close", "because close reflexive(x)")

    elaborate!(program)
  end

  test "operation lists use the already-unwrapped syntax protocol" do
    elaborate!(source("expand(Node(:list, [], [Std.Tactic.simplify(g)]))"))
  end

  test "nested computed requests and oversized operation lists are refused before execution" do
    assert {:invalid_tactic_operation_argument, :exact, _} =
             source("expand(operation(:exact, g, [Node(:tactic_computed_use, [], [])]))")
             |> Program.elaborate()
             |> cause()

    requests = Enum.map_join(1..257, ", ", fn _ -> "Std.Tactic.simplify(g)" end)

    assert {:invalid_tactic_result, :too_many_operations, _} =
             source("expand(Node(:list, [], [#{requests}]))")
             |> Program.elaborate()
             |> cause()
  end

  test "explicit by invocation supports a checked function body before its callback definition" do
    program = source("expand(Std.Tactic.simplify(g))", body: "by close")
    [before, after_callback] = String.split(program, "  fn close_goal")
    [callback, theorem] = String.split(after_callback, "  fn theorem")
    [theorem, ending] = String.split(theorem, "\nend")
    elaborate!(before <> "  fn theorem" <> theorem <> "\n  fn close_goal" <> callback <> "end" <> ending)
  end

  test "source-imported provider hydrates its opaque transitive helpers" do
    dir = Path.join(System.tmp_dir!(), "cure-computed-provider-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)

    File.write!(Path.join(dir, "provider.cure"), """
    mod ComputedProvider
      use Std.Tactic
      use Std.Syntax
      use Std.Bool
      macro Tactics
        tactic inspect_close computed by inspect_goal
      fn inspect_goal(g: Goal) -> MacroResult = match is_equality(g)
        True() -> expand(Std.Tactic.simplify(g))
        False() -> reject_goal("provider refuses")
    end
    """)

    consumer = Path.join(dir, "consumer.cure")

    File.write!(consumer, """
    mod ComputedPhase4
      use ComputedProvider
      use Std.Equivalent
      fn inspect_goal(x: Int) -> Int = x
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because inspect_close
    end
    """)

    assert {:ok, checked} =
             Cure.Compiler.ModulePipeline.check(
               [consumer, Path.join(dir, "provider.cure")],
               package: "computed-test",
               interface_roots: [Cure.Stdlib.Paths.beam_dir()],
               source_roots: [dir]
             )

    env = Map.fetch!(checked.body_envs, {"computed-test", "ComputedPhase4"})
    assert :ok = Kernel.check_def(env, :"ComputedPhase4#theorem")
  end

  test "callback source caches are restored on success and refusal" do
    key = {Cure.Elab.MacroExpand, :callback_cache}
    previous = Process.get(key)
    sentinel = %{outer_request: true}
    Process.put(key, sentinel)

    try do
      elaborate!(source("expand(Std.Tactic.simplify(g))"))
      assert Process.get(key) == sentinel
      assert {:error, _} = Program.elaborate(source(~s|reject_goal("refused")|))
      assert Process.get(key) == sentinel
    after
      if is_nil(previous), do: Process.delete(key), else: Process.put(key, previous)
    end
  end
end
