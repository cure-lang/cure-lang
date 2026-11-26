defmodule Cure.Elab.ProofStateIntegrationTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Cure.Core.{Context, Env, Eval, Kernel}
  alias Cure.Elab.{Program, ProofGoal, ProofState}
  alias Cure.LSP.Server
  alias Cure.Pipeline.Events
  alias Cure.REPL.Session

  @proof """
  mod Observed
    use Std.Equivalent
    fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Int, x, y) = proof chain
      x == y
      because
        have marker = "é𐐀"
        rewrite using h
        exact reflexive(y)
  end
  """

  test "command observations retain named before/after states and checked closure" do
    Events.subscribe(:type_checker, :proof_state)
    assert {{:ok, env}, states} = ProofState.elaborate(@proof, file: "observed.cure")
    assert :ok = Kernel.check_def(env, :"Observed#theorem")
    assert Enum.map(states, & &1.phase) == [:before, :after, :before, :after, :before, :after]
    assert [] = ProofState.remaining(states)

    [_, have_after, rewrite_before, rewrite_after, _, closed] = states
    assert [%{goal: "Equivalent(Int, x, y)", context: context}] = have_after.goals
    assert "marker : String" in context
    assert "h : Equivalent(Int, x, y)" in context
    assert "x : Int" in context
    assert [%{goal: "Equivalent(Int, x, y)"}] = rewrite_before.goals
    assert [%{goal: "Equivalent(Int, y, y)"}] = rewrite_after.goals
    assert [] = closed.goals

    assert_receive {Events, :type_checker, :proof_state, %{phase: :before}, %{file: "observed.cure"}}
    assert_receive {Events, :type_checker, :proof_state, %{phase: :after}, %{file: "observed.cure"}}

    assert {:ok, plain} = Program.elaborate(@proof)
    assert Env.get_def(plain, :"Observed#theorem").body == Env.get_def(env, :"Observed#theorem").body
    assert_receive {Events, :type_checker, :proof_state, %{phase: :before}, %{file: "nofile"}}
    assert_receive {Events, :type_checker, :proof_state, %{phase: :after}, %{file: "nofile"}}
  end

  test "real requests select the command input, transformed output and closure" do
    assert [%{"goal" => "Equivalent(Int, x, y)"}] = request(@proof, position(@proof, "rewrite using h"))

    assert [%{"goal" => "Equivalent(Int, y, y)", "context" => context}] =
             request(@proof, position(@proof, "rewrite using h", :end))

    assert "h : Equivalent(Int, x, y)" in context
    assert [] = request(@proof, position(@proof, "exact reflexive(y)", :end))
    assert [] = request(@proof, %{"line" => 0, "character" => 0})
  end

  test "requests honor UTF-8, UTF-16 and UTF-32 cursor columns" do
    for encoding <- [:utf8, :utf16, :utf32] do
      before_quote = position(@proof, "have marker", :start, encoding)
      assert [%{"context" => before}] = request(@proof, before_quote, encoding)
      refute Enum.any?(before, &String.starts_with?(&1, "marker :"))

      after_quote = position(@proof, ~s(have marker = "é𐐀"), :end, encoding)
      assert [%{"context" => after_context}] = request(@proof, after_quote, encoding)
      assert "marker : String" in after_context
    end
  end

  test "standalone checked solvers expose states without duplicating a command's inner solver call" do
    source = """
    mod DirectSolverView
      use Std.Equivalent
      fn theorem(x: Int, h: Equivalent(Int, x, x)) -> Equivalent(Int, x, x) = by assumption
    end
    """

    assert {{:ok, env}, [before, after_state]} = ProofState.elaborate(source)
    assert %{phase: :before, goals: [%{goal: "Equivalent(Int, x, x)", context: context}]} = before
    assert "h : Equivalent(Int, x, x)" in context
    assert %{phase: :after, goals: []} = after_state
    assert :ok = Kernel.check_def(env, :"DirectSolverView#theorem")
    assert [%{"goal" => "Equivalent(Int, x, x)"}] = request(source, position(source, "by assumption"))
    assert [] = request(source, position(source, "by assumption", :end))

    block = String.replace(source, "= by assumption", "= proof chain\n    x == x\n    because by assumption")
    assert {{:ok, _env}, states} = ProofState.elaborate(block)
    assert Enum.map(states, & &1.phase) == [:before, :after]

    refused = String.replace(source, "Equivalent(Int, x, x) = by assumption", "Equivalent(Int, x, 0) = by assumption")
    assert {{:error, _reason}, [_, %{phase: :failed, goals: [_]}]} = ProofState.elaborate(refused)
  end

  test "initialization advertises the custom server capability" do
    response = transport(%{"method" => "initialize", "id" => 42, "params" => %{}}, %{})
    assert get_in(response, ["result", "capabilities", "experimental", "cure/proofState", "enabled"])
  end

  test "unfinished and failed commands retain the actual residual, not just holes" do
    unfinished = String.replace(@proof, "      exact reflexive(y)\n", "")
    assert {{:error, reason}, states} = ProofState.elaborate(unfinished)
    assert {:proof_chain_mismatch, %{kind: :unfinished_justification}} = Program.semantic_error(reason)
    assert %{phase: :unfinished} = List.last(states)
    assert [%{goal: "Equivalent(Int, y, y)", context: context}] = ProofState.remaining(states)
    assert "h : Equivalent(Int, x, y)" in context
    assert [%{"goal" => "Equivalent(Int, y, y)"}] = Server.proof_state(unfinished)

    failed = String.replace(@proof, "exact reflexive(y)", "exact marker")
    assert {{:error, _}, failed_states} = ProofState.elaborate(failed)
    assert %{phase: :failed, goals: [%{goal: "Equivalent(Int, y, y)"}]} = List.last(failed_states)
  end

  test "individual nested holes use their own checking target and local names" do
    source = """
    mod NestedGoal
      fn convert(input: Int) -> Float = 1.0
      fn later(x: Int) -> Float = convert(?argument)
      fn another() -> Float = ?second
    end
    """

    assert [%{"goal" => "Int", "context" => ["x : Int"]}] =
             request(source, position(source, "?argument"))

    assert [%{"goal" => "Float", "context" => []}] =
             request(source, position(source, "?second"))

    assert {{:ok, env}, states} = ProofState.elaborate(source)
    assert [_, _] = ProofState.remaining(states)
    # Observations do not resolve holes or weaken the code-generation firewall.
    assert Cure.Elab.Erase.has_hole?(Env.get_def(env, :"NestedGoal#later").body)
  end

  test "Session.goals reports actual nested hole targets and open command states" do
    assert {:ok, []} = Session.goals([])

    assert {:definitions, entries} =
             Session.classify("fn convert(input: Int) -> Float = 1.0\nfn later() -> Float = convert(?argument)")

    assert {:ok, [%{goal: "Int", context: []}]} = Session.goals(entries)

    assert {:definitions, entries} = Session.classify(open_declaration())
    assert {:ok, [%{goal: "Equivalent(Int, y, y)", context: context}]} = Session.goals(entries)
    assert "h : Equivalent(Int, x, y)" in context
  end

  test "REPL retains a refused proof for :goals without installing it, and resets it" do
    output =
      capture_io(fn ->
        state = Cure.REPL.__new_state__(error_device: :stdio)
        state = Cure.REPL.__submit__(state, open_declaration())
        state = Cure.REPL.__submit__(state, ";;")
        assert [] = state.defs
        assert [_ | _] = state.proof_states
        state = Cure.REPL.__submit__(state, ":goals")
        state = Cure.REPL.__submit__(state, ":reset")
        assert nil == state.proof_states
        Cure.REPL.__submit__(state, ":goals")
      end)

    assert output =~ "E110"
    assert output =~ "open goals (1)"
    assert output =~ "Equivalent(Int, y, y)"
    assert output =~ "h : Equivalent(Int, x, y)"
    assert output =~ "(no open goals)"
  end

  test "capture restores outer state on nested captures and exceptions" do
    assert {:outer, []} =
             ProofState.capture(fn ->
               assert {{:ok, _}, [_ | _]} = ProofState.elaborate(@proof)

               assert_raise RuntimeError, "capture failure", fn ->
                 ProofState.capture(fn -> raise "capture failure" end)
               end

               :outer
             end)

    assert {:next, []} = ProofState.capture(fn -> :next end)
  end

  test "simp tracing is invocation-local, reports adaptation, and preserves evidence bytes" do
    Events.subscribe(:type_checker, :simp_trace)
    env = equality_env()
    goal = equality_goal(env)
    goal = %{goal | trace: [%{kind: :lemma, name: :"Previous#rule", id: "old"}]}
    plain = {:simplify_command, [], []}
    traced = {:simplify_command, [trace: true, file: "trace.cure", line: 7], []}
    assert {:closed, expected, _} = ProofGoal.command(plain, goal)
    assert {:closed, ^expected, _} = ProofGoal.command(traced, goal)
    assert_receive {Events, :type_checker, :simp_trace, %{lemmas: [], rules: rules}, %{file: "trace.cure", line: 7}}
    refute Enum.any?(rules, &match?(%{id: "old"}, &1))

    source = """
    mod AdaptTrace
      use Std.Equivalent
      fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Int, x, y) = proof chain
        x == y
        because simp? using h
    end
    """

    assert {:ok, traced_env} = Program.elaborate(source, file: "adapt_trace.cure")

    assert_receive {Events, :type_checker, :simp_trace,
                    %{lemmas: [], rules: [%{kind: :proof_adaptation}], command: %{path: "adapt_trace.cure"}},
                    %{file: "adapt_trace.cure"}}

    assert :ok = Kernel.check_def(traced_env, :"AdaptTrace#theorem")
    assert {:ok, plain_env} = Program.elaborate(String.replace(source, "simp?", "simplify"))
    assert Env.get_def(traced_env, :theorem).body == Env.get_def(plain_env, :theorem).body
  end

  test "simp tracing reports progressed explicit rules with the correct source" do
    Events.subscribe(:type_checker, :simp_trace)

    source = """
    mod ExplicitTrace
      use Std.Equivalent
      type Nat = Z | S(Nat)
      fn theorem(x: Nat, y: Nat, h: Equivalent(Nat, S(x), y)) -> Equivalent(Nat, S(S(x)), S(y)) = proof chain
        S(S(x)) == S(y)
        because simp? using [h]
    end
    """

    assert {:ok, env} = Program.elaborate(source, file: "explicit_trace.cure")
    assert :ok = Kernel.check_def(env, :"ExplicitTrace#theorem")
    assert_receive {Events, :type_checker, :simp_trace, %{rules: rules}, %{file: "explicit_trace.cure"}}
    assert Enum.any?(rules, &match?(%{kind: :explicit_rule}, &1))
    assert {:ok, plain} = Program.elaborate(String.replace(source, "simp?", "simplify"))
    assert Env.get_def(plain, :theorem).body == Env.get_def(env, :theorem).body
  end

  test "deferred have facts do not shift the names used for targets or hypothesis types" do
    source = """
    mod NamedHave
      use Std.Equivalent
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because
          have fact: Equivalent(Int, x, x) = reflexive(x)
          exact fact
    end
    """

    assert {{:ok, env}, [_, after_have, _, _]} = ProofState.elaborate(source)
    assert [%{goal: "Equivalent(Int, x, x)", context: context}] = after_have.goals
    assert "fact : Equivalent(Int, x, x)" in context
    assert "x : Int" in context
    refute Enum.any?(context, &String.contains?(&1, "Equivalent(Int, fact, fact)"))
    assert :ok = Kernel.check_def(env, :"NamedHave#theorem")
  end

  test "simp tracing names the ambient lemma only when it actually rewrites" do
    Events.subscribe(:type_checker, :simp_trace)

    source = """
    mod AmbientTrace
      use Std.Equivalent
      type Nat = Z | S(Nat)
      fn plus(left: Nat, right: Nat) -> Nat = match left
        Z() -> right
        S(previous) -> S(plus(previous, right))
      @simp
      fn plus_zero(value: Nat) -> Equivalent(Nat, plus(value, Z()), value) = induction value
        case Z => reflexive(Z())
        case S(previous, ih) => rewrite ih in reflexive(S(previous))
      fn reduced(value: Nat) -> Equivalent(Nat, plus(plus(value, Z()), Z()), value) = proof chain
        plus(plus(value, Z()), Z()) == value
        because simp?
      fn unchanged(value: Nat) -> Equivalent(Nat, value, value) = proof chain
        value == value
        because simp?
    end
    """

    assert {:ok, env} = Program.elaborate(source, file: "ambient_trace.cure")
    assert :ok = Kernel.check_def(env, :"AmbientTrace#reduced")

    assert_receive {Events, :type_checker, :simp_trace,
                    %{lemmas: [:"AmbientTrace#plus_zero", :"AmbientTrace#plus_zero"]}, %{file: "ambient_trace.cure"}}

    assert_receive {Events, :type_checker, :simp_trace, %{lemmas: []}, %{file: "ambient_trace.cure"}}
    assert {:ok, plain} = Program.elaborate(String.replace(source, "simp?", "simplify"))
    assert Env.get_def(plain, :reduced).body == Env.get_def(env, :reduced).body
  end

  defp equality_env do
    assert {:ok, env} =
             Program.elaborate("""
             mod EqualityView
               use Std.Equivalent
               fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
                 x == x
                 because simplify
             end
             """)

    env
  end

  defp equality_goal(env) do
    %{type: {:pi, grade, domain, target}} = Env.get_def(env, :"EqualityView#theorem")
    context = Context.extend(Context.empty(env), Eval.eval(domain, []), grade)
    ProofGoal.new(target, ["x"], context, env)
  end

  defp open_declaration do
    """
    fn theorem(x: Int, y: Int, h: Std.Equivalent.Equivalent(Int, x, y)) -> Std.Equivalent.Equivalent(Int, x, y) = proof chain
      x == y
      because
        rewrite using h
    """
  end

  defp request(source, position, encoding \\ :utf16) do
    response =
      transport(
        %{
          "method" => "cure/proofState",
          "id" => 42,
          "params" => %{"textDocument" => %{"uri" => "file:///observed.cure"}, "position" => position}
        },
        %{documents: %{"file:///observed.cure" => source}, position_encoding: encoding}
      )

    response["result"]["goals"]
  end

  defp transport(message, state) do
    output = capture_io(fn -> Server.process_message(message, state) end)
    [_, json] = String.split(output, "\r\n\r\n", parts: 2)
    :json.decode(json)
  end

  defp position(source, needle, endpoint \\ :start, encoding \\ :utf16) do
    {byte, size} = :binary.match(source, needle)
    prefix = binary_part(source, 0, byte + if(endpoint == :end, do: size, else: 0))
    lines = String.split(prefix, "\n")
    line = List.last(lines)

    character =
      case encoding do
        :utf8 -> byte_size(line)
        :utf16 -> div(byte_size(:unicode.characters_to_binary(line, :utf8, {:utf16, :little})), 2)
        :utf32 -> String.length(line)
      end

    %{"line" => length(lines) - 1, "character" => character}
  end
end
