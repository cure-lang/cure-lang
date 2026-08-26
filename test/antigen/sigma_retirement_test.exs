defmodule Antigen.SigmaRetirementTest do
  @moduledoc """
  D2 retirement antibody. Confirmatory (written AFTER the generators/corpus were
  migrated), so it is expected green on first run:

    (a) the seeded builtin Sigma round-trips — a `mk_pair` intro checks against
        `{:data, :Sigma, …}` and a single-branch projection `:case` ι-reduces to
        the packed component (the inductive replacement for nfst/nsnd);
    (b) the D1 napp accept-pin still holds — a dependent second projection whose
        motive is `b(p.1)` over a context type-family sorts (via the surviving
        `infer_type_value_sort` napp clause), NOT `:bad_motive`;
    (c) the ratchet fires — a hand-built primitive `{:sigma}`/`{:pair}`/`{:fst}`/
        `{:snd}` term is rejected by `Validator` at `no_sigma_node` (asserted via
        `release_config`, already `:reject`).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Builtins, Context, Env, Eval, Inductive, Kernel, Normalise, Validator}

  @nat {:data, :"Std.Nat#Nat", [], []}
  @z {:ctor, :"Std.Nat#Z", []}
  @sz {:ctor, :"Std.Nat#S", [@z]}
  @sigma {:data, :"Std.Sigma#Sigma", [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}

  defp seeded_ctx, do: Context.empty(Builtins.seed(Env.empty()))

  test "(a) mk_pair intro checks against the inductive Sigma and projections ι-reduce" do
    ctx = seeded_ctx()
    assert Inductive.builtin(Context.signature(ctx), :sigma) == :"Std.Sigma#Sigma"

    pair = {:ctor, :"Std.Sigma#mk_pair", [@z, @sz]}
    sigma_value = Eval.eval(@sigma, Context.env(ctx))
    assert :ok = Kernel.check(ctx, pair, sigma_value)

    # First/second projections as single-branch case: ι-reduce to the components.
    fst =
      {:case, pair, {:lam, Cure.Core.Grade.unrestricted(), @sigma, @nat}, [{:"Std.Sigma#mk_pair", 2, {:var, 1}}]}

    snd =
      {:case, pair, {:lam, Cure.Core.Grade.unrestricted(), @sigma, @nat}, [{:"Std.Sigma#mk_pair", 2, {:var, 0}}]}

    assert Normalise.nf(ctx, fst) == @z
    assert Normalise.nf(ctx, snd) == @sz
  end

  test "(b) a dependent second projection sorts via the napp clause (not :bad_motive)" do
    # `recover`'s return index `SF(as, bs, p.1)` and body `p.2` exercise the
    # dependent-projection motive `b(p.1)` whose type-family head is a neutral
    # application — the D1 `infer_type_value_sort({:vneutral, {:napp,…}})` clause.
    src = """
    mod SigmaNappPin
      type Dec = Dcoupled | Causal
      type Sig = CSig | ESig
      type SVDesc = SVNil | SVCons(Sig, SVDesc)
      fn andd(x: Dec, y: Dec) -> Dec = x
      type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
        prim : SF(as, bs, Causal)
        seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
      fn recover({as: SVDesc}, {bs: SVDesc}, p: Sigma(x: Dec, SF(as, bs, x))) -> SF(as, bs, p.1) = p.2
    end
    """

    assert {:ok, env} = Cure.Elab.Program.elaborate(src)
    assert %{body: body} = Env.get_def(env, :recover)
    # No primitive projection node survives in the elaborated body.
    refute has_head?(body, :snd)
    refute has_head?(body, :fst)
  end

  test "(c) the validator rejects every primitive Sigma node at no_sigma_node" do
    for node <- [
          {:sigma, {:type, 0}, {:type, 0}},
          {:pair, @z, @sz},
          {:fst, {:var, 0}},
          {:snd, {:var, 0}}
        ] do
      assert {:error, [%{clause: :no_sigma_node, mode: :reject}]} =
               Validator.validate(node, Validator.release_config())
    end
  end

  defp has_head?(term, tag) when is_tuple(term),
    do: elem(term, 0) == tag or term |> Tuple.to_list() |> Enum.any?(&has_head?(&1, tag))

  defp has_head?(list, tag) when is_list(list), do: Enum.any?(list, &has_head?(&1, tag))
  defp has_head?(_other, _tag), do: false
end
