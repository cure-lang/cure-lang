defmodule Cure.Elab.OmegaSolverTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Eval, Kernel}
  alias Cure.Elab.{Program, Solver}

  defp source(body) do
    "mod OmegaSolverFixture\n  use Std.Proof.LinearArithmetic\n  use Std.Proof.IntOrder\n  use Std.Nat\n  " <>
      String.replace(String.trim(body), "\n", "\n  ") <> "\nend\n"
  end

  defp checked!(body) do
    assert {:ok, env} = Program.elaborate(source(body))
    assert :ok = Kernel.check_def(env, :"OmegaSolverFixture#theorem")
    env
  end

  test "omega reconstructs genuine multihop integer transitivity" do
    checked!("""
    fn theorem(a: Int, b: Int, c: Int, ab: IsLessThanOrEqual(a, b), bc: IsLessThanOrEqual(b, c)) -> IsLessThanOrEqual(a, c) = by omega
    """)
  end

  test "omega reconstructs independent addition and literal natural scaling" do
    for body <- [
          """
          fn theorem(a: Int, b: Int, c: Int, d: Int, ab: IsLessThanOrEqual(a, b), cd: IsLessThanOrEqual(c, d)) -> IsLessThanOrEqual(add_int(a, c), add_int(b, d)) = by omega
          """,
          """
          fn theorem(a: Int, b: Int, ab: IsLessThanOrEqual(a, b)) -> IsLessThanOrEqual(scale_nat_int(S(S(Z())), a), scale_nat_int(S(S(Z())), b)) = by omega
          """
        ] do
      checked!(body)
    end
  end

  test "template omega uses the same checked source path" do
    checked!("""
    macro Tactics
      tactic linear_close becomes by omega
    type Flag = Only
    fn theorem(a: Int, b: Int, h: IsLessThanOrEqual(a, b), flag: Flag) -> IsLessThanOrEqual(a, b) = induction flag
      case Only => linear_close
    """)
  end

  test "false and nonlinear goals refuse rather than converting a Boolean into evidence" do
    for {body, expected} <- [
          {"fn theorem() -> IsLessThanOrEqual(int_one(), int_zero()) = by omega", :omega_no_witness},
          {"fn theorem(a: Int, b: Int) -> IsLessThanOrEqual(multiply_int(a, b), a) = by omega", :outside}
        ] do
      assert {:error, {:proof_chain_mismatch, %{cause: {:solver_failed, :omega, cause}}}} =
               body |> source() |> Program.elaborate() |> Program.semantic_result()

      if expected == :outside,
        do: assert(match?({:omega_outside_fragment, _}, cause)),
        else: assert(cause == expected)
    end
  end

  test "a valid candidate still refuses when the bounded proof reconstruction does not cover the goal" do
    assert {:error, {:proof_chain_mismatch, %{cause: {:solver_failed, :omega, :omega_no_checked_reconstruction}}}} =
             "fn theorem() -> IsLessThan(int_zero(), int_one()) = by omega"
             |> source()
             |> Program.elaborate()
             |> Program.semantic_result()
  end

  test "the actual judgment signature must certify and type-check the checker" do
    env = checked!("fn theorem(a: Int, b: Int, h: IsLessThanOrEqual(a, b)) -> IsLessThanOrEqual(a, b) = h")
    %{type: type} = Env.get_def(env, :theorem)
    {context, expected} = open_telescope(type, Context.empty(env))
    checker = :"Std.Proof.LinearArithmetic#check_lia_candidate"
    command = {:solver_command, [solver: :omega], []}
    uncertified = %{env | certified: MapSet.delete(env.certified, checker)}

    assert {:error, {:proof_chain_mismatch, %{cause: {:solver_failed, :omega, :omega_checker_uncertified}}}} =
             Solver.solve(command, expected, ["h", "b", "a"], %{context | signature: uncertified}, uncertified)

    forged = put_in(env.defs[checker].body, {:ctor, :"Std.Bool#True", []})

    assert {:error, {:proof_chain_mismatch, %{cause: {:solver_failed, :omega, {:omega_checker_rejected, _}}}}} =
             Solver.solve(command, expected, ["h", "b", "a"], %{context | signature: forged}, forged)
  end

  defp open_telescope({:pi, grade, domain, body}, context),
    do: open_telescope(body, Context.extend(context, Eval.eval(domain, Context.env(context)), grade))

  defp open_telescope(target, context), do: {context, target}
end
