defmodule Antigen.Generators.MutationTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Mutation, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  defp sample(gen, n), do: B.interp(gen) |> Enum.take(n)

  # "fst on a Nat" spelled inductively (D2): a projection case over mk_pair
  # scrutinising a Nat — intrinsically ill-typed (case on a non-Sigma), the same
  # :proj_non_pair fault the retired primitive `{:fst, Z}` fixture carried.
  defp proj_on_nat do
    nat = {:data, :Nat, [], []}

    {:case, {:ctor, :Z, []},
     {:lam, Cure.Core.Grade.unrestricted(),
      {:data, :Sigma, [nat, {:lam, Cure.Core.Grade.unrestricted(), nat, nat}], []}, nat}, [{:mk_pair, 2, {:var, 1}}]}
  end

  test "every operator produces a term the kernel REJECTS under infer (construction guarantee)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for kind <- Mutation.operators() do
      {gen, fault} = Mutation.build(ctx, kind)
      assert fault.kind == kind

      for term <- sample(gen, 20) do
        assert {:error, _} = Kernel.infer(ctx, term),
               "operator #{kind} produced an infer-ACCEPTED term: #{inspect(term)}"
      end
    end
  end

  test "each operator's fault carries a kernel-INDEPENDENT witness of ill-typedness" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for kind <- Mutation.operators() do
      {_gen, f} = Mutation.build(ctx, kind)

      case f.witness do
        :head ->
          assert f.expected_head != f.injected_head,
                 "#{kind}: heads must differ (#{inspect(f.expected_head)} vs #{inspect(f.injected_head)})"

        :index ->
          # distinct closed index constructors ⇒ non-convertible, decided syntactically.
          # Laundered through heads_differ?/2 so the 1.20 checker doesn't fold this
          # (deliberately disjoint) comparison to a constant — the runtime check is real.
          assert heads_differ?(f.expected_head, f.injected_head)

        :level ->
          {:type, req} = f.expected_head
          {:type, act} = f.injected_head
          assert act > req, "#{kind}: injected level must exceed required (predicativity)"

        :scope ->
          {k, gamma_len} = f.scope
          assert k >= gamma_len, "#{kind}: var index must be out of scope"
      end
    end
  end

  test "mutant/0 emits a well-formed :mutant_term challenge that the kernel rejects" do
    alias Antigen.Challenge

    for c <- sample(Mutation.mutant(), 60) do
      assert %Challenge{kind: :mutant_term, assay: "mutation/rejection", label: :ill_typed, payload: p} = c
      assert p.sig == :v1
      assert p.fault.kind in Mutation.operators()
      env = SigMenu.env_of(:v1)
      ctx = SigMenu.rebuild_context(env, p.ctx)
      # generation totality + rejection
      assert {:error, _} = Kernel.infer(ctx, p.term)
    end
  end

  test "each wrapper is non-contaminating and fault-driven (deterministic, fixed filler)" do
    ctx = Context.empty(SigMenu.env_of(:v1))
    # well-typed Nat
    wt = {:ctor, :Z, []}
    # intrinsically ill-typed
    fault = proj_on_nat()

    for kind <- Mutation.wrappers() do
      assert {:ok, _} = Kernel.infer(ctx, Mutation.wrap(wt, kind, wt)),
             "wrapper #{kind} contaminated a well-typed inner"

      assert {:error, _} = Kernel.infer(ctx, Mutation.wrap(fault, kind, wt)),
             "wrapper #{kind} did not propagate the inner fault"
    end
  end

  test "a fixed deep wrapper stack stays well-typed and propagates a fault (composition)" do
    ctx = Context.empty(SigMenu.env_of(:v1))
    wt = {:ctor, :Z, []}
    fault = proj_on_nat()
    # fold every wrapper kind, innermost-first, with a fixed Nat filler
    stack = fn inner -> Enum.reduce(Mutation.wrappers(), inner, fn k, acc -> Mutation.wrap(acc, k, wt) end) end

    assert {:ok, _} = Kernel.infer(ctx, stack.(wt)), "deep fixed stack contaminated a well-typed inner"
    assert {:error, _} = Kernel.infer(ctx, stack.(fault)), "deep fixed stack swallowed the fault"
  end

  test "every operator and every wrapper kind is reachable by construction (deterministic)" do
    ctx = Context.empty(SigMenu.env_of(:v1))
    # each operator's build deterministically records its own fault kind
    kinds = Enum.map(Mutation.operators(), fn op -> elem(Mutation.build(ctx, op), 1).kind end)
    assert Enum.sort(kinds) == Enum.sort(Mutation.operators())
    # each wrapper kind applies without error and yields a distinct well-formed term
    # (inner != filler: :case_scrut's branch body ignores the filler and :case_branch's
    # scrutinee ignores the inner, so inner == filler would make those two wrapper
    # outputs byte-identical and collapse the uniq count to 4 — verified by direct
    # run with inner = filler = {:ctor,:Z,[]})
    terms = Enum.map(Mutation.wrappers(), fn k -> Mutation.wrap({:ctor, :Z, []}, k, {:ctor, :S, [{:ctor, :Z, []}]}) end)
    assert length(Enum.uniq(terms)) == length(Mutation.wrappers())
    assert Enum.all?(terms, &Cure.Core.Term.term?/1)
  end

  test "mutant/0 emits deep mutants: depth/wrap_path recorded, still rejected, depth reached" do
    depths =
      for c <- sample(Mutation.mutant(), 300) do
        p = c.payload
        assert length(p.fault.wrap_path) == p.fault.depth
        assert p.fault.depth >= 0 and p.fault.depth <= Mutation.max_depth()
        assert Enum.all?(p.fault.wrap_path, &(&1 in Mutation.wrappers()))
        env = SigMenu.env_of(:v1)
        ctx = SigMenu.rebuild_context(env, p.ctx)
        assert {:error, _} = Kernel.infer(ctx, p.term)
        p.fault.depth
      end

    # deep mutants actually generated
    assert Enum.max(depths) >= 4
  end

  # -- Tier-B reach expansion: new-type-former mutation operators --------------
  # Each is self-wrapped (no `deepen` — its non-Nat-typed pre-wrap would
  # contaminate the Nat->Nat deepen layers), and each has a load-bearing
  # analog-accepted test proving the fault is genuinely introduced, not a
  # wrapper artifact.

  test "pair_component builds a check-embedded ill-typed pair the kernel rejects" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    {gen, fault} = Mutation.build(ctx, :pair_component)
    assert fault.kind == :pair_component

    for mutant <- sample(gen, 5) do
      # never a bare :pair (would crash Kernel.infer)
      refute match?({:pair, _, _}, mutant)
      assert {:error, _} = Kernel.infer(ctx, mutant)
    end
  end

  test "pair_component's well-typed analog is accepted (operator genuinely ill-types)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    # Inductive spelling (D2): identity-app over Sigma(Nat, λ_.Nat) checking a
    # well-typed mk_pair — the same check-embedded shape as the operator's output.
    nat = {:data, :Nat, [], []}

    good =
      {:app,
       {:lam, Cure.Core.Grade.unrestricted(),
        {:data, :Sigma, [nat, {:lam, Cure.Core.Grade.unrestricted(), nat, nat}], []}, {:var, 0}},
       {:ctor, :mk_pair, [{:ctor, :Z, []}, {:ctor, :Z, []}]}}

    assert {:ok, _} = Kernel.infer(ctx, good)
  end

  test "app_result builds a function whose result violates its declared codomain, rejected" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    {gen, fault} = Mutation.build(ctx, :app_result)
    assert fault.kind == :app_result
    for mutant <- sample(gen, 5), do: assert({:error, _} = Kernel.infer(ctx, mutant))
  end

  test "app_result's well-typed analog is accepted (operator genuinely ill-types)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    good_fun = {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:ctor, :Z, []}}
    pi_t = {:pi, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}}
    good = {:app, {:lam, Cure.Core.Grade.unrestricted(), pi_t, {:app, {:var, 0}, {:ctor, :Z, []}}}, good_fun}
    assert {:ok, _} = Kernel.infer(ctx, good)
  end

  test "type_param_mismatch: Cons of a wrong-param element into List(Nat), rejected" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    {gen, fault} = Mutation.build(ctx, :type_param_mismatch)
    assert fault.kind == :type_param_mismatch

    for mutant <- sample(gen, 5) do
      # never bare (→ :ctor_requires_checking_mode)
      refute match?({:ctor, :Cons, _}, mutant)
      assert {:error, _} = Kernel.infer(ctx, mutant)
    end
  end

  test "type_param_mismatch's well-typed analog is accepted (List check-mode accepts a correct Cons)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    list_nat = {:data, :List, [{:data, :Nat, [], []}], []}

    good =
      {:app, {:lam, Cure.Core.Grade.unrestricted(), list_nat, {:var, 0}},
       {:ctor, :Cons, [{:ctor, :Z, []}, {:ctor, :Nil, []}]}}

    assert {:ok, _} = Kernel.infer(ctx, good)
  end

  # term()-typed inequality: erases the operands' narrowed types so the 1.20
  # checker can't prove the comparison constant (see the :index witness case).
  defp heads_differ?(a, b), do: a != b
end
