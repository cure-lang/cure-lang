defmodule Antigen.Generators.Mutation do
  @moduledoc """
  Ill-typed Core term generator (spec §5). Each operator builds a self-contained
  CHECKED scaffold — a minimal well-typed enclosing form wrapping exactly one
  construction-guaranteed-wrong subterm — so `Kernel.infer` rejects it at that
  enclosing check (never a bare wrong-headed term, which would infer fine). The
  well-typed filler parts are drawn from the lazy `Term.gen_term`, keeping mutants
  deep and realistic. Backend-free: built only via the `Antigen.Gen` DSL.
  """
  alias Antigen.Challenge
  alias Antigen.Gen
  alias Antigen.Generators.Context, as: CtxGen
  alias Antigen.Generators.{SigMenu, Term}
  alias Cure.Core.Context

  @operators [
    :head_swap,
    :ctor_arg,
    :index_mismatch,
    :app_domain,
    :out_of_scope_var,
    :proj_non_pair,
    :universe,
    :pair_component,
    :app_result,
    :type_param_mismatch
  ]
  def operators, do: @operators

  # Self-wrapped operators for the new type formers (Σ/Π/List): each already
  # embeds its fault in an identity-application against the target type (so a bare
  # :pair / param-bearing :ctor never reaches Kernel.infer without a checking
  # frame). Their pre-wrap is NOT Nat-typed, so they must NOT be run through
  # `deepen` (whose Nat->Nat layers would type-error at the wrapper boundary and
  # contaminate the fault). `mutant/0` forces depth 0 for these (spec §5).
  @self_wrapped [:pair_component, :app_result, :type_param_mismatch]
  def self_wrapped, do: @self_wrapped

  # menu term helpers (kernel term literals; do not use SigMenu privates)
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}
  defp vnil, do: {:ctor, :vnil, []}
  defp nat_t, do: {:data, :Nat, [], []}
  defp vec(i), do: {:data, :Vec, [], [i]}

  # well-typed filler generators. `gnat` occasionally reuses a banked closed Nat
  # (crossover, spec §3) when a seed pool is installed in the process dictionary;
  # with no pool installed (all existing tests), it is byte-identical to today.
  defp gnat(ctx) do
    fresh = Term.gen_term(ctx, nat_t())

    case Process.get(:antigen_seed_pool) do
      %{} = pool ->
        case Antigen.Generators.SeedPool.pool_gen(pool, nat_t()) do
          :none -> fresh
          g -> Gen.frequency([{4, fresh}, {1, g}])
        end

      _ ->
        fresh
    end
  end

  # : Vec Z
  defp gvec0(ctx), do: Term.gen_term(ctx, vec(z()))
  # : Vec (S Z)
  defp gvec_sz(ctx), do: Term.gen_term(ctx, vec(s(z())))

  @doc "Build `{Gen.t(term), fault}` for `kind` in the local context `ctx`."
  @spec build(Context.t(), atom()) :: {Gen.t(), map()}
  def build(ctx, :head_swap) do
    g =
      Gen.bind(gvec0(ctx), fn v ->
        Gen.bind(gnat(ctx), fn n ->
          # plus expects Nat, given Vec
          Gen.return({:app, {:app, {:global, :plus}, v}, n})
        end)
      end)

    {g, %{kind: :head_swap, witness: :head, expected_head: :Nat, injected_head: :Vec, scope: nil}}
  end

  def build(ctx, :ctor_arg) do
    g =
      Gen.bind(gnat(ctx), fn n ->
        Gen.bind(gvec0(ctx), fn v ->
          # x should be Nat, given Vec
          Gen.return({:ctor, :vcons, [n, v, vnil()]})
        end)
      end)

    {g, %{kind: :ctor_arg, witness: :head, expected_head: :Nat, injected_head: :Vec, scope: nil}}
  end

  def build(ctx, :index_mismatch) do
    g =
      Gen.bind(gnat(ctx), fn n ->
        Gen.bind(gvec_sz(ctx), fn tail ->
          # n=Z ⇒ tail must be Vec Z; given Vec (S Z)
          Gen.return({:ctor, :vcons, [z(), n, tail]})
        end)
      end)

    {g, %{kind: :index_mismatch, witness: :index, expected_head: :Z, injected_head: :S, scope: nil}}
  end

  def build(ctx, :app_domain) do
    g =
      Gen.bind(gvec0(ctx), fn v ->
        # (λx:Nat.x) applied to Vec
        Gen.return({:app, {:lam, Cure.Core.Grade.unrestricted(), nat_t(), {:var, 0}}, v})
      end)

    {g, %{kind: :app_domain, witness: :head, expected_head: :Nat, injected_head: :Vec, scope: nil}}
  end

  def build(ctx, :out_of_scope_var) do
    gamma_len = Context.length(ctx)
    # always ≥ |Γ|
    g = Gen.bind(Gen.int(0, 3), fn d -> Gen.return({:var, gamma_len + d}) end)
    # witness records the minimal certain out-of-scope index (d = 0).
    {g,
     %{kind: :out_of_scope_var, witness: :scope, expected_head: nil, injected_head: nil, scope: {gamma_len, gamma_len}}}
  end

  def build(_ctx, :proj_non_pair) do
    # fst on a Nat: a :case with a Sigma motive + mk_pair branch scrutinising a
    # Nat is ill-typed (case on a non-Sigma) — the same proj-non-pair fault.
    g =
      Gen.bind(Gen.int(0, 3), fn k ->
        Gen.return(
          {:case, nat_numeral(k), {:lam, Cure.Core.Grade.unrestricted(), sig(), nat_t()}, [{:mk_pair, 2, {:var, 1}}]}
        )
      end)

    {g, %{kind: :proj_non_pair, witness: :head, expected_head: :Sigma, injected_head: :Nat, scope: nil}}
  end

  def build(_ctx, :universe) do
    t0 = {:type, 0}
    # Equivalent's param telescope demands a : Type₀; feeding Type₀ itself
    # (whose sort is Type₁ ⋠ Type₀) is the universe fault, carried by the
    # inductive identity former (the retired primitive {:eq} carried it before).
    g = Gen.return({:data, :Equivalent, [t0], [t0, t0]})
    {g, %{kind: :universe, witness: :level, expected_head: {:type, 0}, injected_head: {:type, 1}, scope: nil}}
  end

  # ── Tier-B new-type-former operators (self-wrapped, spec §5) ──────────────────
  # Each embeds its fault in an identity application against the target type so
  # Kernel.infer reaches it in CHECK mode (a bare :pair / param-bearing :ctor has
  # no infer path). They are listed in @self_wrapped and bypass `deepen`.

  def build(_ctx, :pair_component) do
    # Σ Nat. Nat expects both components Nat; a Bd (T) in the first slot violates
    # it. The identity-app forces Kernel.infer to CHECK the pair against Σ Nat.Nat.
    # T : Bd, not Nat
    bad_pair = {:ctor, :mk_pair, [{:ctor, :T, []}, z()]}
    g = Gen.return({:app, {:lam, Cure.Core.Grade.unrestricted(), sig(), {:var, 0}}, bad_pair})
    {g, %{kind: :pair_component, witness: :head, expected_head: :Nat, injected_head: :Bd, scope: nil}}
  end

  def build(_ctx, :app_result) do
    # (λ x:Nat. T) has body T : Bd, violating the declared codomain Nat. Applied
    # through an identity-Pi wrapper so `check` compares the Bd body against Nat
    # (distinct fault class from app_domain, which breaks the domain).
    # body T : Bd, not Nat
    bad_fun = {:lam, Cure.Core.Grade.unrestricted(), nat_t(), {:ctor, :T, []}}
    pi_t = {:pi, Cure.Core.Grade.unrestricted(), nat_t(), nat_t()}
    g = Gen.return({:app, {:lam, Cure.Core.Grade.unrestricted(), pi_t, {:app, {:var, 0}, z()}}, bad_fun})
    {g, %{kind: :app_result, witness: :head, expected_head: :Nat, injected_head: :Bd, scope: nil}}
  end

  def build(_ctx, :type_param_mismatch) do
    # Cons (T:Bd) Nil : List(Nat) — the element T : Bd violates the List(Nat)
    # parameter. Check-embedded (a bare param-ctor → :ctor_requires_checking_mode).
    list_nat = {:data, :List, [nat_t()], []}
    bad_cons = {:ctor, :Cons, [{:ctor, :T, []}, {:ctor, :Nil, []}]}
    g = Gen.return({:app, {:lam, Cure.Core.Grade.unrestricted(), list_nat, {:var, 0}}, bad_cons})
    {g, %{kind: :type_param_mismatch, witness: :head, expected_head: :Nat, injected_head: :Bd, scope: nil}}
  end

  defp nat_numeral(0), do: z()
  defp nat_numeral(k), do: s(nat_numeral(k - 1))

  # ── Deep propagation (sub-project A) ──────────────────────────────────────────
  # Bury a fault under `depth` nested well-typed CHECKED contexts so `infer` must
  # thread its rejection up `depth` distinct error-propagation paths. Every wrapper
  # is Nat→Nat (hole expects Nat, term produces Nat), so any composition is
  # well-typed EXCEPT at the innermost hole — the rejection is provably fault-driven,
  # not a wrapper-internal type error (see the uncontaminated-control test).
  @wrappers [:app_arg, :ctor_nat, :case_scrut, :case_branch, :pair]
  def wrappers, do: @wrappers

  @max_depth 8
  def max_depth, do: @max_depth

  defp sig, do: {:data, :Sigma, [nat_t(), {:lam, Cure.Core.Grade.unrestricted(), nat_t(), nat_t()}], []}
  defp motive, do: {:lam, Cure.Core.Grade.unrestricted(), nat_t(), nat_t()}
  defp nat_branches(zbody), do: [{:Z, 0, zbody}, {:S, 1, {:var, 0}}]

  @doc """
  Wrap `term` in `depth` Nat→Nat checked layers. `Gen` of `{deep_term, wrap_path}`
  where `wrap_path` (length == depth) lists the wrapper kinds innermost-first.
  """
  @spec deepen(Context.t(), term(), non_neg_integer()) :: Gen.t()
  def deepen(_ctx, term, 0), do: Gen.return({term, []})

  def deepen(ctx, term, depth) when depth > 0 do
    Gen.bind(Gen.frequency(Enum.map(@wrappers, fn k -> {1, Gen.return(k)} end)), fn kind ->
      Gen.bind(apply_wrapper(ctx, term, kind), fn wrapped ->
        Gen.bind(deepen(ctx, wrapped, depth - 1), fn {outer, path} ->
          Gen.return({outer, [kind | path]})
        end)
      end)
    end)
  end

  @doc "Pure application of one Nat→Nat wrapper with an explicit Nat `filler`."
  def wrap(inner, :app_arg, filler), do: {:app, {:app, {:global, :plus}, inner}, filler}
  def wrap(inner, :ctor_nat, _filler), do: {:ctor, :S, [inner]}
  def wrap(inner, :case_scrut, _filler), do: {:case, inner, motive(), nat_branches(z())}
  def wrap(inner, :case_branch, filler), do: {:case, filler, motive(), nat_branches(inner)}

  def wrap(inner, :pair, filler),
    do: {:app, {:lam, Cure.Core.Grade.unrestricted(), sig(), z()}, {:ctor, :mk_pair, [inner, filler]}}

  # Each wrapper places `inner` at a Nat-checked hole; filler is a well-typed Nat.
  # :app_arg/:case_branch/:pair draw a well-typed Nat filler; :ctor_nat/:case_scrut ignore it.
  defp apply_wrapper(ctx, inner, kind) when kind in [:app_arg, :case_branch, :pair],
    do: Gen.bind(gnat(ctx), fn f -> Gen.return(wrap(inner, kind, f)) end)

  defp apply_wrapper(_ctx, inner, kind),
    do: Gen.return(wrap(inner, kind, z()))

  def assay_id, do: "mutation/rejection"

  @doc "A `Gen` of a `:mutant_term` challenge."
  @spec mutant() :: Gen.t()
  def mutant do
    env = SigMenu.env_of(:v1)

    Gen.bind(CtxGen.gen(env), fn ctx_types ->
      ctx = SigMenu.rebuild_context(env, ctx_types)

      Gen.bind(select(), fn kind ->
        {term_gen, fault} = build(ctx, kind)

        Gen.bind(term_gen, fn term ->
          Gen.bind(depth_gen(kind), fn d ->
            Gen.bind(deepen(ctx, term, d), fn {deep_term, wrap_path} ->
              fault = Map.merge(fault, %{depth: d, wrap_path: wrap_path})

              Gen.return(
                Challenge.new(
                  kind: :mutant_term,
                  assay: assay_id(),
                  label: :ill_typed,
                  payload: %{sig: :v1, ctx: ctx_types, type: goal_of(fault), term: deep_term, fault: fault}
                )
              )
            end)
          end)
        end)
      end)
    end)
  end

  @spec default_gen() :: Gen.t()
  def default_gen, do: mutant()

  # Uniform weighted choice over all 7 operators (each is self-contained, so all
  # are applicable at every draw — spec §5's "applicable set" is the full set once
  # operators own their checked scaffolds). Equal weights keep the diversity floor
  # (Task 7) comfortably reachable.
  defp select, do: Gen.frequency(Enum.map(@operators, fn k -> {1, Gen.return(k)} end))

  # Self-wrapped operators submit their fault pre-wrapped (non-Nat-typed) and must
  # not be deepened; every other operator deepens uniformly over [0, max_depth].
  defp depth_gen(kind) do
    if kind in @self_wrapped, do: Gen.return(0), else: Gen.int(0, max_depth())
  end

  # The challenge-level `type` field is documentation-only (spec §4/§6.1): a
  # nominal goal describing the fault site, never a proven property of the mutant.
  defp goal_of(%{kind: :universe}), do: {:type, 0}
  defp goal_of(%{kind: :index_mismatch}), do: vec(z())
  defp goal_of(%{expected_head: :Sigma}), do: sig()
  defp goal_of(%{expected_head: :Nat}), do: nat_t()
  defp goal_of(_), do: nat_t()
end
