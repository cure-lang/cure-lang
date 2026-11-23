defmodule Cure.Elab.Phase4ClosureAuditTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.{Program, ProofState}

  @parameters """
  x: Int, y: Int, z: Int,
  consume: (Equivalent(Int, x, y), Equivalent(Int, y, z)) -> Equivalent(Int, x, z),
  left: Equivalent(Int, x, y), right: Equivalent(Int, y, z)
  """

  defp program(commands, extra \\ "", parameters \\ @parameters) do
    commands = commands |> String.trim() |> String.replace("\n", "\n      ")
    extra = extra |> String.trim() |> String.replace("\n", "\n  ")

    """
    mod Phase4ClosureAudit
      use Std.Equivalent
      use Std.Nat

      #{extra}

      fn theorem(#{String.trim(parameters)}) -> Equivalent(Int, x, z) = proof chain
        x == z
        because
          #{commands}
    end
    """
  end

  defp checked(source) do
    assert {:ok, env} = Program.elaborate(source)
    assert %{body: _} = Env.get_def(env, :"Phase4ClosureAudit#theorem")
    assert :ok = Kernel.check_def(env, :"Phase4ClosureAudit#theorem")
    env
  end

  defp same_body(left, right) do
    assert Env.get_def(left, :"Phase4ClosureAudit#theorem").body ==
             Env.get_def(right, :"Phase4ClosureAudit#theorem").body
  end

  test "two independent premises close in order and reconstruct the handwritten application" do
    manual = checked(program("exact consume(left, right)"))

    applied =
      checked(
        program("""
        apply consume
        exact left
        exact right
        """)
      )

    same_body(applied, manual)

    for commands <- [
          "apply consume\nexact left",
          "apply consume\nexact right\nexact left",
          "apply consume\nexact left\nexact left"
        ] do
      assert {:error, _} = Program.elaborate(program(commands))
    end
  end

  test "nested applications retain both parents and the outer sibling" do
    parameters = """
    x: Int, y: Int, z: Int,
    consume: (Equivalent(Int, x, y), Equivalent(Int, y, z)) -> Equivalent(Int, x, z),
    build: (Equivalent(Int, x, x), Equivalent(Int, y, y)) -> Equivalent(Int, x, y),
    first: Equivalent(Int, x, x), second: Equivalent(Int, y, y), right: Equivalent(Int, y, z)
    """

    manual = checked(program("exact consume(build(first, second), right)", "", parameters))

    applied =
      checked(
        program(
          """
          apply consume
          apply build
          exact first
          exact second
          exact right
          """,
          "",
          parameters
        )
      )

    same_body(applied, manual)
  end

  test "unresolved implicit witnesses become explicit typed obligations before dependent premises" do
    parameters = """
    x: Int, y: Int, z: Int,
    left: Equivalent(Int, x, y), right: Equivalent(Int, y, z)
    """

    manual = checked(program("exact trans(left, right)", "", parameters))

    applied =
      checked(
        program(
          """
          apply trans
          exact y
          exact left
          exact right
          """,
          "",
          parameters
        )
      )

    same_body(applied, manual)
  end

  test "value-dependent premises use the actual earlier witness" do
    make_source = fn witness, proof ->
      """
      mod Phase4ClosureAudit
        use Std.Equivalent
        use Std.Nat

        fn choose(x: Int, witness: Nat, evidence: Equivalent(Nat, witness, Z())) -> Equivalent(Int, x, x) =
          reflexive(x)

        fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
          x == x
          because
            apply choose(x)
            exact #{witness}
            exact #{proof}
      end
      """
    end

    checked(make_source.("Z()", "reflexive(Z())"))
    assert {:error, _} = Program.elaborate(make_source.("S(Z())", "reflexive(Z())"))
  end

  test "proof-dependent premises are instantiated only after their evidence closes" do
    checked("""
    mod Phase4ClosureAudit
      use Std.Equivalent

      fn need(
        x: Int,
        first: Equivalent(Int, x, x),
        second: Equivalent(Equivalent(Int, x, x), first, first)
      ) -> Equivalent(Int, x, x) = first

      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because
          apply need(x)
          exact reflexive(x)
          exact reflexive(reflexive(x))
    end
    """)
  end

  test "ambient type variables remain in scope beneath a function-valued premise binder" do
    checked("""
    mod Phase4ClosureAudit
      use Std.Equivalent

      fn need(
        {a: Type}, value: a, f: (a) -> a,
        evidence: Equivalent(a, f(value), value)
      ) -> Equivalent(a, value, value) = reflexive(value)

      fn theorem({a: Type}, value: a) -> Equivalent(a, value, value) = proof chain
        value == value
        because
          apply need(value)
          exact fn(item) -> item
          exact reflexive(value)
    end
    """)
  end

  test "a computed operation sequence uses the same focused multi-premise runner" do
    extra = """
    use Std.Tactic
    use Std.Syntax

    macro Tactics
      tactic finish computed by finish_goal

    fn finish_goal(g: Goal) -> MacroResult = expand(Node(:list, [], [
      Std.Tactic.apply(g, variable("consume")),
      Std.Tactic.exact(g, variable("left")),
      Std.Tactic.exact(g, variable("right"))
    ]))
    """

    manual = checked(program("exact consume(left, right)", extra))
    applied = checked(program("finish", extra))
    same_body(applied, manual)
  end

  test "authoritative session snapshots retain all siblings without stale child frontiers" do
    source =
      program("""
      apply consume
      exact left
      exact right
      """)

    assert {{:ok, env}, observations} =
             ProofState.capture(fn -> Program.elaborate(source, file: "closure-audit.cure") end)

    assert :ok = Kernel.check_def(env, :"Phase4ClosureAudit#theorem")

    after_steps =
      Enum.filter(observations, fn state ->
        state.kind == :session and state.phase == :after
      end)

    assert [
             %{goals: [first, second]},
             %{goals: [remaining]},
             %{goals: []}
           ] = after_steps

    refute first.id == second.id
    assert remaining.id == second.id
    assert [] = ProofState.remaining(observations)
  end
end
