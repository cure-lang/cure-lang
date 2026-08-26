defmodule Cure.Elab.DependentMatchSurfaceTest do
  @moduledoc """
  Surface acceptance for sub-project ④ (spec §2, §6). Programs go through the
  real pipeline via Cure.Elab.Program.elaborate/1. Negatives assert the exact
  error atom (spec §7).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  alias Cure.Core.{Env, Validator}

  @vec """
  type Nat = Z | S(Nat)
  type Vector(a: Type) indices (n: Nat)
    empty : Vector(a, Z)
    prepend : a -> Vector(a, n) -> Vector(a, S(n))
  """

  # Pre-impl: {:error, :coverage}. Post: {:ok, _} — prepend is unreachable at Z,
  # so the elaborator discharges it and the kernel's coverage check passes.
  test "(A) a match omitting an impossible constructor elaborates" do
    src =
      @vec <>
        """
        fn only_empty({a: Type}, xs: Vector(a, Z)) -> Nat = match xs
          empty() -> Z()
        """

    assert {:ok, _env} = Program.elaborate(src)
  end

  # Pre-impl: {:error, :coverage} (kernel). Post: {:error, {:missing_branch, :prepend}}.
  test "(A) a match omitting a REACHABLE constructor is a missing-branch error" do
    src =
      @vec <>
        """
        fn bad({a: Type}, {n: Nat}, xs: Vector(a, n)) -> Nat = match xs
          empty() -> Z()
        """

    assert {:error, {:source_context, {:missing_branch, :"Main#prepend"}, _}} = Program.elaborate(src)
  end

  # Pre-impl: {:error, :unknown_global} (impossible lexes as an identifier body).
  # Post: {:ok, _} — the branch is genuinely unreachable and accepted.
  test "(A) an explicit `-> impossible` on an unreachable branch elaborates" do
    src =
      @vec <>
        """
        fn ei({a: Type}, xs: Vector(a, Z)) -> Nat = match xs
          empty() -> Z()
          prepend(x, rest) -> impossible
        """

    assert {:ok, _env} = Program.elaborate(src)
  end

  # K4 §H step 2: an impossible constructor is OMITTED from Core, not given an
  # {:absurd} placeholder body. The kernel's partial-coverage (step 1) accepts the
  # omission; no {:absurd} node should survive into the elaborated Core term.
  test "(A) an impossible constructor is omitted from Core, not marked {:absurd}" do
    src =
      @vec <>
        """
        fn only_empty({a: Type}, xs: Vector(a, Z)) -> Nat = match xs
          empty() -> Z()
        """

    assert {:ok, env} = Program.elaborate(src)
    nodes = env |> Env.get_def(:only_empty) |> Map.fetch!(:body) |> Validator.nodes()
    refute Enum.any?(nodes, &match?({:absurd}, &1)), "impossible branch must be omitted, not {:absurd}"

    case_nodes = Enum.filter(nodes, &match?({:case, _, _, _}, &1))

    assert Enum.any?(case_nodes, fn {:case, _, _, brs} ->
             Enum.map(brs, &elem(&1, 0)) == [:"Main#empty"]
           end),
           "the case should carry only the reachable :empty branch"
  end

  # Pre-impl: {:error, :unknown_global}. Post: {:error, {:reachable_impossible, :prepend}}.
  test "(A) a mis-marked `-> impossible` on a reachable branch is rejected" do
    src =
      @vec <>
        """
        fn mi({a: Type}, {n: Nat}, xs: Vector(a, n)) -> Nat = match xs
          empty() -> Z()
          prepend(x, rest) -> impossible
        """

    assert {:error, {:source_context, {:reachable_impossible, :"Main#prepend"}, _}} = Program.elaborate(src)
  end

  test "an impossible nested branch is discharged from the matched family's indices" do
    src = """
    mod NestedIndexedImpossible
      use Std.List

      type State = Active(Nat) | Accepted

      type Path indices (input: List(Nat), state: State)
        Finished : Path(Nil(), Accepted())

      fn reject_finished(input: List(Nat), source: Nat, path: Path(input, Active(source))) -> Nat = match input
        Nil() -> match path
          Finished() -> impossible
        Cons(_, _) -> match path
          Finished() -> impossible
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
