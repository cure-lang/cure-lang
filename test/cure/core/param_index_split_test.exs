defmodule Cure.Core.ParamIndexSplitTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel}

  @type0 {:type, 0}
  @dec {:data, :Dec, [], []}

  # P(a: Type) indices (n: Dec) with wrap : (p: a) -> P(a, Causal).
  # In the ctor telescope check_ctor binds params first (a), then args (p):
  #   ctx_full = [a, p]  → a is {:var, 1} (num_args=1 + (num_params-1-0)=0).
  # result_params = [a] = [{:var, 1}]; result_indices = [Causal].
  defp param_env do
    Env.empty()
    |> Inductive.declare(
      Inductive.family(:Dec, [], [], 0),
      [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
    )
    |> Inductive.declare(
      Inductive.family(:P, [{:a, @type0}], [{:n, @dec}], 1),
      [
        Inductive.ctor(:wrap, [{:p, {:var, 0}}], [{:ctor, :Causal, []}], [:unrestricted], [{:var, 1}])
      ]
    )
  end

  test "family carries a non-empty parameter telescope and param_count" do
    env = param_env()
    assert Inductive.param_telescope(env, :P) == [{:a, @type0}]
    assert Inductive.index_telescope(env, :P) == [{:n, @dec}]
    assert Inductive.param_count(env, :P) == 1
    assert Inductive.param_count(env, :Dec) == 0
  end

  test "constructor records result_params and result_indices separately" do
    env = param_env()
    assert Inductive.ctor_result_params(env, :wrap) == [{:var, 1}]
    assert Inductive.ctor_result_indices(env, :wrap) == [{:ctor, :Causal, []}]
  end

  test "3- and 4-arity ctor builders default result_params to []" do
    c3 = Inductive.ctor(:mk, [], [])
    c4 = Inductive.ctor(:mk, [], [], [])
    assert c3.result_params == []
    assert c4.result_params == []
  end

  alias Cure.Core.Inductive, as: Ind

  test "check_ctor accepts a uniform parameter constructor" do
    env = param_env()
    fam = Ind.get_family(env, :P)
    ctor = Ind.get_ctor(env, :wrap)
    assert :ok == Kernel.check_ctor(env, fam, ctor)
  end

  test "check_ctor rejects a non-uniform parameter (param slot is not a)" do
    # oddball : P(Bool-ish stand-in, Causal) — param slot is a GROUND family, not
    # the parameter variable a. Use Dcoupled-indexed Dec as a stand-in rigid term.
    env = param_env()
    fam = Ind.get_family(env, :P)

    bad =
      Ind.ctor(:oddball, [], [{:ctor, :Causal, []}], [], [{:data, :Dec, [], []}])

    assert {:error, {:non_uniform_parameter, info}} = Kernel.check_ctor(env, fam, bad)
    assert info.family == :P and info.ctor == :oddball and info.position == 0
  end

  test "check_ctor on a param-free family is unchanged (regression)" do
    env = param_env()
    fam = Ind.get_family(env, :Dec)
    assert :ok == Kernel.check_ctor(env, fam, Ind.get_ctor(env, :Causal))
  end

  test "check_ctor rejects a result_params arity mismatch (wrong count, not just wrong value)" do
    env = param_env()
    fam = Ind.get_family(env, :P)
    # `wrong_arity` supplies zero result_params where the family declares 1 —
    # exercises check_uniform_params' `:arity` branch, which the position-mismatch
    # test above never reaches (it always supplies exactly 1 result_param).
    wrong_arity = Ind.ctor(:wrong_arity, [], [{:ctor, :Causal, []}], [], [])
    assert {:error, {:non_uniform_parameter, info}} = Kernel.check_ctor(env, fam, wrong_arity)
    assert info.family == :P and info.ctor == :wrong_arity and info.position == :arity
  end

  alias Cure.Core.Context

  test "checking a param-bearing constructor application against its expected vdata carries params ++ indices" do
    env = param_env()
    ctx = Context.empty(env)
    a_val = {:vdata, :Dec, []}
    causal_val = {:vctor, :Causal, []}
    term = {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}
    expected = {:vdata, :P, [a_val, causal_val]}
    assert :ok == Kernel.check(ctx, term, expected)
  end

  test "bare inference of a param-bearing constructor application is rejected (no expected type to source params from)" do
    env = param_env()
    ctx = Context.empty(env)
    term = {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}
    assert {:error, {:ctor_requires_checking_mode, :P}} == Kernel.infer(ctx, term)
  end

  test "infer of a param-free constructor is unchanged (regression)" do
    env = param_env()
    ctx = Context.empty(env)
    assert {:ok, {:vdata, :Dec, []}} == Kernel.infer(ctx, {:ctor, :Dcoupled, []})
  end

  test "checking against a mismatched expected vdata is rejected (args checking ok is not enough)" do
    # wrap(d) always produces index Causal — checking it against an expected
    # type whose index is Dcoupled must fail, even though `d` itself checks
    # fine against the parameter slot. Falsifies a clause that only verifies
    # check_ctor_app succeeds without comparing the computed result to `expected`.
    env = param_env()
    ctx = Context.empty(env)
    a_val = {:vdata, :Dec, []}
    causal_val = {:vctor, :Causal, []}
    wrong_index_val = {:vctor, :Dcoupled, []}
    term = {:ctor, :wrap, [{:ctor, :Dcoupled, []}]}
    expected = {:vdata, :P, [a_val, wrong_index_val]}

    assert {:error, {:conversion_failure, {:vdata, :P, [^a_val, ^causal_val]}, ^expected}} =
             Kernel.check(ctx, term, expected)
  end

  # Test 1 (spec §7.1): a parameter survives matching unchanged. Match on a
  # P(a, Causal); in the wrap branch, a hypothesis h : a is still usable at type a
  # (the parameter is NOT refined away by the match).
  test "a parameter-typed hypothesis is reusable in a branch (param not matched)" do
    env = param_env()
    # def probe : Π(a:Type). Π(h:a). Π(v:P(a,Causal)). a
    #   = λa.λh.λv. case v of wrap(p) -> h
    # de Bruijn under [a,h] (2 bindings, h=var0/a=var1): P(a, Causal) for the `v`
    # binder's own type sits at the same depth in both def_type's third Pi domain
    # and body's third lambda domain — no shift between them.
    p_ac = {:data, :P, [{:var, 1}], [{:ctor, :Causal, []}]}

    def_type =
      {:pi, Cure.Core.Grade.unrestricted(), @type0,
       {:pi, Cure.Core.Grade.unrestricted(), {:var, 0}, {:pi, Cure.Core.Grade.unrestricted(), p_ac, {:var, 2}}}}

    # motive : λ(n:Dec). λ(x:P(a,n)). a — abstracts index_arity+1 = 2 args.
    # Case context here is [v,h,a] (v=0/h=1/a=2); adding the motive's [x,n]
    # binders gives [x,n,v,h,a]: a is var4, the index binder n is var0.
    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :P, [{:var, 3}], [{:var, 0}]}, {:var, 4}}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @type0,
       {:lam, Cure.Core.Grade.unrestricted(), {:var, 0},
        {:lam, Cure.Core.Grade.unrestricted(), p_ac, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 2}}]}}}}

    env = Env.add_def(env, :probe, def_type, body)
    assert :ok == Kernel.check_def(env, :probe)
  end

  # Test 4 (spec §7.4): param-free family behaves exactly as before.
  test "param-free family case is unchanged" do
    env =
      Env.empty()
      |> Inductive.declare(
        Inductive.family(:Dec, [], [], 0),
        [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
      )
      |> Inductive.declare(
        Inductive.family(:Box, [], [{:d, @dec}], 0),
        [Inductive.ctor(:mk, [{:x, @dec}], [{:var, 0}])]
      )

    box_causal = {:data, :Box, [], [{:ctor, :Causal, []}]}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Box, [], [{:var, 0}]}, @dec}}

    def_type = {:pi, Cure.Core.Grade.unrestricted(), box_causal, @dec}
    body = {:lam, Cure.Core.Grade.unrestricted(), box_causal, {:case, {:var, 0}, motive, [{:mk, 1, {:var, 0}}]}}
    env = Env.add_def(env, :probe2, def_type, body)
    assert :ok == Kernel.check_def(env, :probe2)
  end

  # Branch-path instance of the scoping gap: a pattern-bound argument whose
  # declared type is the family's own parameter (Vector's `prepend`'s `x : a`
  # shape) must be usable at that parameter's type inside the branch body.
  test "a branch's pattern variable typed at the family parameter has the correct type" do
    env = param_env()
    # def probe3 : Π(a:Type). Π(v:P(a,Causal)). a = λa.λv. case v of wrap(p) -> p
    p_ac0 = {:data, :P, [{:var, 0}], [{:ctor, :Causal, []}]}
    def_type = {:pi, Cure.Core.Grade.unrestricted(), @type0, {:pi, Cure.Core.Grade.unrestricted(), p_ac0, {:var, 1}}}

    motive =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), {:data, :P, [{:var, 2}], [{:var, 0}]}, {:var, 3}}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @type0,
       {:lam, Cure.Core.Grade.unrestricted(), p_ac0, {:case, {:var, 0}, motive, [{:wrap, 1, {:var, 0}}]}}}

    env = Env.add_def(env, :probe3, def_type, body)
    assert :ok == Kernel.check_def(env, :probe3)
  end
end
