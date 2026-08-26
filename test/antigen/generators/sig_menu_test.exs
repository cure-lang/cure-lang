defmodule Antigen.Generators.SigMenuTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Env, Inductive, Context, Kernel, Eval}

  test "env_of(:v1) certifies plus and dbl through the real certifier" do
    env = SigMenu.env_of(:v1)
    assert Env.certified?(env, :plus)
    assert Env.certified?(env, :dbl)
    # families present (get_family/2 is on Inductive, not Env — see Reference)
    assert Inductive.get_family(env, :Nat)
    assert Inductive.get_family(env, :Bd)
    assert Inductive.get_family(env, :Vec)
  end

  test "env_of(:v1) seeds the Bool builtin (True/False) for prim comparison/connective typing" do
    env = SigMenu.env_of(:v1)
    assert Inductive.get_family(env, :Bool)
    # the :bool builtin key resolves to the Bool family — bool_type_value needs this
    assert Inductive.builtin(env, :bool) == :Bool
    ctx = Context.empty(env)
    # a comparison SPINE (K2) types at Bool and normalizes to a True/False ctor
    lt = {:app, {:app, {:global, :int_lt}, {:int_lit, 1}}, {:int_lit, 2}}
    true_ctor = Cure.Elab.Name.qualify("Std.Bool", :True)
    assert {:ok, _} = Kernel.infer(ctx, lt)
    assert {:ctor, ^true_ctor, []} = Cure.Core.Normalise.nf(ctx, lt, fuel: 500_000, delta: :certified)
  end

  test "canon builds a well-typed inhabitant for each closed goal type" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    for goal <- SigMenu.goal_types() do
      assert SigMenu.inhabitable?(ctx, goal)
      term = SigMenu.canon(ctx, goal)
      # canon's contract is "a term that CHECKS at the goal" — use check-mode
      # directly rather than infer-then-check, since check-mode-only inhabitants
      # (a bare param-bearing `Nil`/`Cons`, a bare `:pair`) have no infer path.
      # `check/3`'s type argument is a VALUE, so evaluate the goal term first.
      goal_val = Eval.eval(goal, Context.env(ctx))
      assert Kernel.check(ctx, term, goal_val) == :ok
    end
  end

  test "canon handles a stuck-indexed Vec via a matching context variable" do
    env = SigMenu.env_of(:v1)
    # Γ = [ n : Nat, xs : Vec(n) ]  (kernel order: xs innermost = index 0)
    ctx = SigMenu.rebuild_context(env, [SigMenu.vec({:var, 0}), SigMenu.nat()])
    # Vec(n), n = index 1 from the body
    goal = SigMenu.vec({:var, 1})
    assert SigMenu.inhabitable?(ctx, goal)
    term = SigMenu.canon(ctx, goal)
    assert {:ok, _} = Kernel.infer(ctx, term)
  end

  # -- Tier-B reach expansion: List(A) parametric family (Task 1) --------------

  test "env_of(:v1) registers the List(A) family with Nil/Cons" do
    env = SigMenu.env_of(:v1)
    assert Inductive.param_count(env, :List) == 1
    assert Inductive.ctor_quantities(env, :Nil) != nil
    assert Inductive.ctor_quantities(env, :Cons) != nil
  end

  test "List(Nat) is inhabitable and canon gives Nil" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    list_nat = {:data, :List, [SigMenu.nat()], []}
    assert SigMenu.inhabitable?(ctx, list_nat)
    assert SigMenu.canon(ctx, list_nat) == {:ctor, :Nil, []}
  end

  # The only Task-1 test that exercises the kernel on a param-bearing checking-mode
  # term — the one that catches a missing/wrong `result_params`. List is check-mode-
  # only at the top level (a bare param-ctor never infers — kernel.ex), so wrap in
  # an identity application (same trick Task 6/8 use).
  test "Cons/Nil check-mode-accept against List(Nat) (result_params correctness)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    list_nat = {:data, :List, [SigMenu.nat()], []}
    nil_wrapped = {:app, {:lam, Cure.Core.Grade.unrestricted(), list_nat, {:var, 0}}, {:ctor, :Nil, []}}

    cons_wrapped =
      {:app, {:lam, Cure.Core.Grade.unrestricted(), list_nat, {:var, 0}},
       {:ctor, :Cons, [{:ctor, :Z, []}, {:ctor, :Nil, []}]}}

    assert {:ok, _} = Kernel.infer(ctx, nil_wrapped)
    assert {:ok, _} = Kernel.infer(ctx, cons_wrapped)
  end

  # -- Task 2: List introduction rule + goal seeds ----------------------------

  test "gen_term over List(Nat) produces a List constructor" do
    alias Antigen.Generators.Term
    alias Antigen.Backend.StreamData, as: SD
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    gen = Term.gen_term(ctx, {:data, :List, [SigMenu.nat()], []})
    terms = SD.sample(SD.interp(gen), 20)
    # the List intro rule now fires — Nil/Cons appear in the sample (the generator
    # also legitimately reaches List goals via case/var eliminations, so `any?`,
    # not `all?`).
    assert Enum.any?(terms, fn t -> match?({:ctor, :Nil, []}, t) or match?({:ctor, :Cons, _}, t) end)
  end

  test "typed_term challenges over List goals are infer-viable at the top level" do
    alias Antigen.Generators.Term
    alias Antigen.Backend.StreamData, as: SD

    for id <- Term.assay_ids() do
      samples = SD.interp(Term.typed_term(id)) |> Enum.take(80)
      list_samples = Enum.filter(samples, &match?({:data, :List, _, _}, &1.payload.type))
      assert list_samples != [], "no List sample drawn in 80 tries for #{id}"

      for c <- list_samples do
        env = SigMenu.env_of(:v1)
        ctx = SigMenu.rebuild_context(env, c.payload.ctx)

        assert {:ok, _} = Kernel.infer(ctx, c.payload.term),
               "top-level List challenge term not infer-viable: #{inspect(c.payload.term)}"
      end
    end
  end

  # -- Task 3: Pi/Sigma goal seeds (Pi re-enabled after the nf idempotence fix) --

  test "goal_types includes Pi and Sigma seeds; all seeds inhabitable + canon total" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    seeds = SigMenu.goal_types()
    assert Enum.any?(seeds, &match?({:data, :Sigma, _, _}, &1))
    assert Enum.any?(seeds, &match?({:pi, _g, _, _}, &1))

    for g <- seeds do
      assert SigMenu.inhabitable?(ctx, g), "non-inhabitable seed: #{inspect(g)}"
      # canon must not raise
      assert SigMenu.canon(ctx, g)
    end
  end

  # -- Task 4: mark vcons's length witness n as :erased -----------------------

  test "vcons declares its length witness n as :erased (so erase is not identity)" do
    env = SigMenu.env_of(:v1)
    assert Inductive.ctor_quantities(env, :vcons) == [:erased, :unrestricted, :unrestricted]
  end

  test "gen_term over a Pi goal produces a lambda" do
    alias Antigen.Generators.Term
    alias Antigen.Backend.StreamData, as: SD
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)
    gen = Term.gen_term(ctx, {:pi, Cure.Core.Grade.unrestricted(), SigMenu.nat(), SigMenu.nat()})
    terms = SD.sample(SD.interp(gen), 10)
    assert Enum.any?(terms, &match?({:lam, _g, _, _}, &1))
  end
end
