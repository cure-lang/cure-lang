defmodule Antigen.Generators.EffectInert do
  @moduledoc """
  Generator for the `kernel/effect_inert` law (`Antigen.Assays.KernelLaw`): the
  `Effect` type former and its `pure`/`bind` term formers are an **inert,
  uninterpreted signature** — the kernel types them and compares them by
  structural congruence, but NOTHING reduces them (design
  `2026-07-09-effect-type-former-design.md` §3.2, §9).

  Three Core nodes carry the signature:

      {:effect_type, t}    Effect(T)   — the type former
      {:effect_pure, a}    pure(a)     — a trivial computation
      {:effect_bind, e, k} bind(e, k)  — sequencing; `k` is an ordinary Core
                                         `{:lam, ω, dom, body}`, non-dependent

  Each challenge carries one well-typed effect term (type `Effect(Int)`); the
  assay asserts the *inertness invariance* the spec's verification gate demands:

    * `nf(t)` preserves the effect **skeleton** — the arrangement and nesting of
      `pure`/`bind`/`Effect` nodes is unchanged, even though nf may still reduce
      ordinary *sub*terms (an `Effect(Int)` payload redex reduces; the `pure`
      around it does not). A monad law (`bind(pure a, k) → k a`) or a commuting
      conversion would change that skeleton and the property would fire.

    * the definitional inequality `bind(pure(a), k) ≢ k(a)` and
      `bind(pure(a), k) ≢ pure(a)` — the *left identity* that must NOT hold. If a
      future edit reduced `bind(pure(a), k)` to `k(a)` in `Eval`/`Conv`/`Normalise`,
      the two would become convertible and this antibody would catch it.

  The shape menu below IS the coverage: a bare `Effect(T)`, a bare `pure`, a
  `pure` over a payload redex (so nf demonstrably reduces subterms while leaving
  `pure` intact), the load-bearing `bind(pure(a), λx. pure(x))`, a `bind`-over-
  `pure` with a NON-trivial continuation (so `k(a)` differs from both `pure(a)`
  and the bind itself — a genuinely distinct left-identity check), and a
  `bind`-over-`bind` (nesting, the commuting-conversion catcher).
  """
  alias Antigen.{Gen, Challenge}

  @omega Cure.Core.Grade.unrestricted()
  @int {:data, :Int, [], []}
  @effect_int {:effect_type, {:data, :Int, [], []}}

  # `pure(x)` where x is the nearest bound var (de Bruijn 0).
  @pure_var0 {:effect_pure, {:var, 0}}
  # A payload redex `(λx:Int. x) 3` — reduces to `3` under nf, exercising the
  # rule that nf evaluates an effect node's *subterms* while leaving the effect
  # structure itself untouched.
  @payload_redex {:app, {:lam, @omega, @int, {:var, 0}}, {:int_lit, 3}}
  # pure(3) : Effect(Int)
  @pure3 {:effect_pure, {:int_lit, 3}}
  # λ x:Int. pure(x) : Int -> Effect(Int)
  @k_pure {:lam, @omega, @int, @pure_var0}

  # {result_type, term, note}, paired 1:1 with a cover cell below.
  @cases [
    {@effect_int, @effect_int, "bare Effect(Int): the type former is inert"},
    {@effect_int, @pure3, "pure(3): a trivial computation"},
    {@effect_int, {:effect_pure, @payload_redex}, "pure((λx.x) 3): nf reduces the PAYLOAD, leaves `pure` intact"},
    {@effect_int, {:effect_bind, @pure3, @k_pure},
     "bind(pure(3), λx. pure(x)): the left-identity redex that must NOT reduce"},
    {@effect_int, {:effect_bind, @pure3, {:lam, @omega, @int, {:effect_bind, @pure_var0, @k_pure}}},
     "bind(pure(3), λx. bind(pure(x), λy. pure(y))): k(a) ≠ pure(a), a distinct check"},
    {@effect_int, {:effect_bind, {:effect_bind, @pure3, @k_pure}, @k_pure},
     "bind(bind(pure(3), λx. pure(x)), λy. pure(y)): nesting (commuting-conversion catcher)"}
  ]

  @cells [
    :effect_type,
    :pure,
    :pure_redex_payload,
    :bind_over_pure,
    :bind_over_pure_nontrivial_k,
    :nested_bind
  ]

  @doc """
  Shape-coverage cells for the manifest gate (`Antigen.CoverManifest`) — one per
  effect shape; the gate confirms every cell is produced by `gen/0`.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells, do: for(cell <- @cells, do: {"kernel/effect_inert", cell})

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(Enum.zip(@cases, @cells)), fn {{type, term, note}, cell} ->
      Gen.return(
        Challenge.new(
          kind: :typed_term,
          assay: "kernel/effect_inert",
          label: :well_typed,
          payload: %{sig: :v1, ctx: [], type: type, term: term},
          note: note,
          cover_tag: cell
        )
      )
    end)
  end

  @doc "The literal case menu (for the generator's coverage self-test)."
  def cases, do: @cases
end
