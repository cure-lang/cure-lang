defmodule Cure.Elab.ProofHoleResolutionTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # These fixtures exercise the resolver's TAG-GATING over a LOCAL proposition
  # (`IsFoo`) that no stdlib module proves. That isolation is deliberate: once
  # `Std.Proof.Math` ships its `@lemma`-tagged
  # `multiplying_positive_numbers_is_positive` (the Task 9 stdlib demo), the goal
  # `IsPositive(multiply(a, b))` is auto-provable ambiently — so a fixture written
  # over that goal could never demonstrate a DECLINE (the stdlib lemma discharges
  # it) and would collide with any local duplicate (two tagged lemmas, one goal →
  # a genuine ambiguity). A fresh proposition under a head no stdlib lemma is filed
  # under keeps the local `@lemma` tag the ONLY thing that decides resolution,
  # while still driving the real cross-module refinement-projection path: `FooNat`
  # is a `Std.Refine` Sigma refinement, so the lemma's `IsFoo(refined_value …)`
  # hypotheses are discharged by `refinement_proof` projections exactly as the
  # shipped `PositiveNatural` demo is.
  #
  # A LOCAL, UNTAGGED lemma. No @lemma anywhere → the argument-position hole
  # must REACH the resolver (proving it is no longer the raw
  # {:unsupported_expression,...} rejection of before), and the resolver DECLINES
  # (nothing tagged). Under first-class holes (Slice 1), a declined proof hole
  # does NOT abort elaboration: it SURVIVES as a stuck `{:hole, id}` neutral.
  # The enclosing `refine(...)` application evals to a stuck spine and the kernel
  # accepts the hole at the proof goal, so the program type-checks with an
  # inspectable hole that blocks codegen — mirroring a body-level hole, rather
  # than crashing the hole-blind evaluator (which no longer exists) or raising a
  # hard error. This proves resolution is gated on the tag AND that a declined
  # auto-proof is deferrable, not fatal.
  @red """
  mod RedUntagged
    use Std.Nat
    use Std.Refine

    type IsFoo indices (value: Nat)
      FooEvidence : IsFoo(S(predecessor))

    type FooNat = {value: Nat | IsFoo(value)}

    fn foo_combines({left: Nat}, {right: Nat},
          lp: IsFoo(left), rp: IsFoo(right)) -> IsFoo(plus(left, right)) = match lp
      FooEvidence() -> FooEvidence()

    fn demo(left: FooNat, right: FooNat) -> FooNat =
      refine(plus(refined_value(left), refined_value(right)), ?)
  end
  """

  # Recursively search an elaborated Core term for a surviving hole node.
  defp has_hole?({:hole, _id}), do: true
  defp has_hole?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_hole?/1)
  defp has_hole?(l) when is_list(l), do: Enum.any?(l, &has_hole?/1)
  defp has_hole?(m) when is_map(m), do: m |> Map.values() |> Enum.any?(&has_hole?/1)
  defp has_hole?(_), do: false

  test "an untagged proof hole is DECLINED and survives as a first-class hole" do
    assert {:ok, env} = Program.elaborate(@red)

    demo =
      env.defs
      |> Map.values()
      |> Enum.find(fn d -> to_string(d.name) |> String.ends_with?("demo") end)

    assert demo, "demo/2 must be elaborated"

    assert has_hole?(demo.body),
           "a declined proof hole must SURVIVE in the elaborated body, not vanish or error"

    # The surviving hole type-checks but must NOT be emittable: the codegen gate
    # refuses the whole program until the hole is filled.
    assert {:error, {:unfilled_hole, details}} = Program.check_codegen_ready(env)
    assert to_string(details.definition) |> String.contains?("demo")

    assert binary_part(@red, details.span.start_byte, details.span.end_byte - details.span.start_byte) ==
             "?"
  end

  # Identical to @red but the local lemma is TAGGED @lemma. Now the hole must be
  # discharged automatically: sub-goals IsFoo(refined_value(left/right)) come from
  # the refinement projections of the two FooNat binders.
  #
  # CRITICAL: @green and @reference use the SAME module name (`TaggedDemo`).
  # Global def names are module-qualified, so the LOCAL lemma `foo_combines` would
  # resolve to a DIFFERENT global atom in each program if the two modules had
  # different names — making `demo_body(green_env) == demo_body(ref_env)`
  # structurally false no matter how correct ProofSearch is. Each `elaborate`
  # builds an independent Env from scratch, so reusing the name is safe.
  @green """
  mod TaggedDemo
    use Std.Nat
    use Std.Refine

    type IsFoo indices (value: Nat)
      FooEvidence : IsFoo(S(predecessor))

    type FooNat = {value: Nat | IsFoo(value)}

    @lemma
    fn foo_combines({left: Nat}, {right: Nat},
          lp: IsFoo(left), rp: IsFoo(right)) -> IsFoo(plus(left, right)) = match lp
      FooEvidence() -> FooEvidence()

    fn demo(left: FooNat, right: FooNat) -> FooNat =
      refine(plus(refined_value(left), refined_value(right)), ?)
  end
  """

  # Same program, same module name, but the proof is written BY HAND (no hole).
  # Its `demo` body is the reference the resolved term must equal.
  @reference """
  mod TaggedDemo
    use Std.Nat
    use Std.Refine

    type IsFoo indices (value: Nat)
      FooEvidence : IsFoo(S(predecessor))

    type FooNat = {value: Nat | IsFoo(value)}

    @lemma
    fn foo_combines({left: Nat}, {right: Nat},
          lp: IsFoo(left), rp: IsFoo(right)) -> IsFoo(plus(left, right)) = match lp
      FooEvidence() -> FooEvidence()

    fn demo(left: FooNat, right: FooNat) -> FooNat =
      refine(plus(refined_value(left), refined_value(right)),
             foo_combines(refinement_proof(left), refinement_proof(right)))
  end
  """

  defp demo_body(env) do
    {_name, %{body: body}} =
      Enum.find(env.defs, fn {name, _} -> Atom.to_string(name) |> String.ends_with?("demo") end)

    body
  end

  test "tagging the lemma discharges the hole and the program passes the codegen gate" do
    assert {:ok, env} = Program.elaborate(@green)
    assert :ok = Program.check_codegen_ready(env)
  end

  test "the found proof term equals the hand-written proof term (same-run differential)" do
    {:ok, green_env} = Program.elaborate(@green)
    {:ok, ref_env} = Program.elaborate(@reference)

    assert demo_body(green_env) == demo_body(ref_env)
  end

  # An ARGUMENT-position declined hole (the `elaborate_expr_checked({:hole,…})`
  # trigger, elaborator.ex, distinct from the body-level `elaborate_body` hole
  # clause in declarations.ex) must ALSO get a def-qualified id when the SAME
  # named hole is declined in two different functions of one module — otherwise
  # the two declined proof obligations, which have DIFFERENT goal types
  # (`IsFoo(plus(a,b))` in `demo_left` vs `IsFoo(plus(c,d))` in `demo_right`),
  # would collapse to one `Conv`-equal neutral (the same cross-def collision the
  # body-hole case guards against, exercised through the OTHER hole_id call site).
  @two_untagged_named_holes """
  mod TwoUntaggedArgHoles
    use Std.Nat
    use Std.Refine

    type IsFoo indices (value: Nat)
      FooEvidence : IsFoo(S(predecessor))

    type FooNat = {value: Nat | IsFoo(value)}

    fn demo_left(left: FooNat, right: FooNat) -> FooNat =
      refine(plus(refined_value(left), refined_value(right)), ?p)

    fn demo_right(left: FooNat, right: FooNat) -> FooNat =
      refine(plus(refined_value(left), refined_value(right)), ?p)
  end
  """

  defp hole_ids_in(term) do
    case term do
      {:hole, id} -> [id]
      t when is_tuple(t) -> t |> Tuple.to_list() |> Enum.flat_map(&hole_ids_in/1)
      l when is_list(l) -> Enum.flat_map(l, &hole_ids_in/1)
      _ -> []
    end
  end

  test "the same named argument-position hole in two different defs gets distinct ids" do
    assert {:ok, env} = Program.elaborate(@two_untagged_named_holes)

    ids =
      env.defs
      |> Enum.filter(fn {name, _definition} -> Cure.Elab.Name.owner(name) == env.module_owner end)
      |> Enum.map(&elem(&1, 1))
      |> Enum.flat_map(fn %{body: body} -> hole_ids_in(body) end)

    assert length(ids) == 2

    assert length(Enum.uniq(ids)) == 2,
           "CROSS-DEF ARGUMENT-HOLE COLLISION: `?p` in demo_left and `?p` in " <>
             "demo_right minted the SAME id #{inspect(ids)}"
  end
end
