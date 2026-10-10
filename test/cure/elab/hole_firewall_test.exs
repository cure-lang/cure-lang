defmodule Cure.Elab.HoleFirewallTest do
  @moduledoc """
  The typed-hole firewall (docs/KERNEL.md): a `{:hole, name}` term typechecks
  against any expected type but **blocks codegen** — no beam is emitted for a
  definition that still contains one.

  Regression guard for the reported soundness/workflow gap: a reachable,
  unfilled hole at a VALUE type was silently auto-filled by the proof search's
  local-context source. `fn f(n: Nat) -> Nat = ?goal` elaborated to `λn. n`
  (the local `n : Nat` "proved" the goal `Nat`), so the hole vanished before the
  codegen gate and the program ran with the hole never filled.

  The fix scopes the proof search's bare-local-variable source to PROPOSITION
  goals (proof-irrelevant types): a local of a proof-relevant value type is a
  value, not a proof, and must never fill a hole. Proof obligations
  (`IsTrue(x > 0)`, `IsPositive(n)`) still discharge as before.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  defp has_hole?({:hole, _}), do: true
  defp has_hole?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_hole?/1)
  defp has_hole?(l) when is_list(l), do: Enum.any?(l, &has_hole?/1)
  defp has_hole?(m) when is_map(m), do: m |> Map.values() |> Enum.any?(&has_hole?/1)
  defp has_hole?(_), do: false

  defp def_body(env, suffix) do
    {_name, %{body: body}} =
      Enum.find(env.defs, fn {name, _d} -> Atom.to_string(name) |> String.ends_with?(suffix) end)

    body
  end

  # The exact reported reproduction: a whole-body hole at a declared VALUE
  # return type, with a same-typed local binder in scope. The local must NOT
  # discharge it.
  @body_hole """
  mod HoleCall
    use Std.Nat
    fn f(n: Nat) -> Nat = ?goal
  end
  """

  # The same defect through the ARGUMENT-position hole trigger: a hole at a
  # value argument position, with a same-typed local binder in scope.
  @arg_hole """
  mod HoleArg
    use Std.Nat
    fn g(a: Nat, b: Nat) -> Nat = a
    fn f(n: Nat) -> Nat = g(n, ?hole)
  end
  """

  test "a whole-body hole at a value type is NOT auto-filled by a same-typed local" do
    assert {:ok, env} = Program.elaborate(@body_hole)

    assert has_hole?(def_body(env, "HoleCall#f")),
           "the value-position hole must SURVIVE in the elaborated body"

    assert {:error, {:unfilled_hole, details}} = Program.check_codegen_ready(env)
    assert to_string(details.definition) |> String.contains?("f")
  end

  test "an argument-position hole at a value type is NOT auto-filled by a same-typed local" do
    assert {:ok, env} = Program.elaborate(@arg_hole)

    assert has_hole?(def_body(env, "HoleArg#f")),
           "the value-position argument hole must SURVIVE in the elaborated body"

    assert {:error, {:unfilled_hole, _details}} = Program.check_codegen_ready(env)
  end

  # The load-bearing legitimate case the firewall must NOT break: a hole whose
  # goal is a PROPOSITION is still discharged by a matching local hypothesis.
  @proof_obligation """
  mod RefineWireEvidence
    use Std.Nat
    use Std.Bool
    use Std.Proof.IntMath
    fn wrap(x: Int, evidence: IsTrue(x > 0)) -> {n: Int | n > 0} = x
  end
  """

  test "a proposition goal is still discharged by a matching local hypothesis" do
    assert {:ok, env} = Program.elaborate(@proof_obligation)
    assert :ok = Program.check_codegen_ready(env)
  end

  # A hole still TYPECHECKS (development proceeds around it) — only codegen is
  # blocked. This is the documented split: `cure check` is OK, `cure run`/emit
  # refuses. Pinned so a future change cannot make the hole a hard elaboration
  # error (which would break the inspectable-hole workflow).
  test "a value-position hole still typechecks; only codegen is refused" do
    assert {:ok, _env} = Program.elaborate(@body_hole)
  end

  # The gating is on the GOAL's proof-relevance, not on the local: a bare local
  # of a proof-relevant family (`Nat`) is never a proof, while a bare local of a
  # proposition family is. Exercised directly through the resolver so the
  # boundary is pinned independently of the elaboration surface.
  test "the bare-local source fires for a proposition goal but not a value goal" do
    alias Cure.Core.{Context, Env, Eval, Inductive}
    alias Cure.Elab.ProofSearch

    # A one-constructor, no-argument family is a proposition; a two-constructor
    # family is a proof-relevant value type.
    prop_env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:PropFamily, [], [], 0), [Inductive.ctor(:mkProp, [], [])])
      |> Inductive.declare(Inductive.family(:ValFamily, [], [], 0), [
        Inductive.ctor(:mkA, [], []),
        Inductive.ctor(:mkB, [], [])
      ])

    prop_goal = {:data, :PropFamily, [], []}
    val_goal = {:data, :ValFamily, [], []}

    prop_ctx = Context.empty(prop_env) |> Context.extend(Eval.eval(prop_goal, []))
    val_ctx = Context.empty(prop_env) |> Context.extend(Eval.eval(val_goal, []))

    assert {:ok, {:var, 0}} = ProofSearch.resolve(prop_goal, prop_ctx, prop_env)
    assert :none = ProofSearch.resolve(val_goal, val_ctx, prop_env)
  end
end
