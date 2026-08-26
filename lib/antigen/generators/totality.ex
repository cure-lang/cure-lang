defmodule Antigen.Generators.Totality do
  @moduledoc """
  Known-label totality generator (spec §5.1). Emits `:def_group` challenges whose
  ground-truth label (`:terminating` | `:diverging`) is correct **by construction**
  — the generator IS the oracle (umbrella §6), so the deterministic constructors
  below are cross-checked against the real certifier in the Task-12 self-tests.

  Def/family names are a fixed, literal, closed set (`:f`, `:g`, `:h`) so the atoms
  exist the instant this module is loaded — required for `:safe` corpus replay in a
  process that never ran the generator (see `Antigen.Corpus`, Task 5 safety note).
  """
  alias Antigen.{Gen, Challenge}
  alias Cure.Core.Env

  @doc """
  Coverage-manifest cells (`Antigen.CoverManifest`) — a soundness-relevant subset
  of the `gen/1`-reachable def-group shapes across both assay ids. `:pending_sibling`
  is the premature-certification finding cell (a mutual member judged while a sibling
  body is still an elaborator placeholder), which the always-complete-env sampling
  never reached.
  """
  @spec cover_cells() :: [{String.t(), atom()}]
  def cover_cells do
    [
      {"totality/diverging", :diverging_mutual},
      {"totality/diverging", :reconstruct_equal},
      {"totality/diverging", :nullary_self},
      {"totality/diverging", :nullary_mutual},
      {"totality/diverging", :pending_sibling},
      {"totality/terminating", :structural},
      {"totality/terminating", :two_arg},
      {"totality/terminating", :mutual_accept}
    ]
  end

  @dec {:data, :Dec, [], []}
  @nat {:data, :Nat, [], []}

  @doc "A Gen program over the known-label def groups."
  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.frequency([
      {1, Gen.return(diverging_mutual_pair())},
      {1, Gen.return(structural_terminating())},
      # richer certifier drivers — cover Certificate.walk_node's per-former arms,
      # non-var scrutinee refinement, arg_relation's ctor/catch-all arms, and the
      # mixed change-matrix closure (see each constructor's @doc).
      {1, Gen.return(enriched_terminating())},
      {1, Gen.return(nonvar_scrutinee_terminating())},
      {1, Gen.return(reconstruct_equal_diverging())},
      {1, Gen.return(unknown_arg_diverging())},
      {1, Gen.return(two_arg_terminating())},
      # mutual-group accept path + matrix-closure / empty-dimension edges
      {1, Gen.return(terminating_mutual_pair())},
      {1, Gen.return(swap_terminating())},
      {1, Gen.return(nullary_self_loop())},
      {1, Gen.return(nullary_mutual_loop())},
      # premature-certification guard: an earlier mutual member must not be certified
      # while a sibling body is still a pending placeholder.
      {1, Gen.return(diverging_pending_sibling())}
    ])
  end

  @doc """
  The banked 2-cycle: `f = λx. g x`, `g = λx. f x` over `Dec → Dec`. Neither body
  references its own name, so single-body analysis alone cannot witness the cycle;
  `Cure.Core.Certificate` detects it through the signature (mutual-cycle detection,
  the fix for the once-live hole — see `d13d718`) and certifies neither. The pair
  genuinely diverges under δ. Label `:diverging`. Kept forever as the permanent
  regression guard for that fix.
  """
  @spec diverging_mutual_pair() :: Challenge.t()
  def diverging_mutual_pair do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}
    bf = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :g}, {:var, 0}}}
    bg = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [%{name: :f, type: ty, body: bf}, %{name: :g, type: ty, body: bg}],
        focus: [:f, :g]
      },
      note: "mutual cycle f->g->f (hole fixed d13d718; permanent regression guard)",
      cover_tag: :diverging_mutual
    )
  end

  @doc """
  A diverging mutual pair whose sibling body is still an elaborator PENDING
  placeholder — the mid-body_pass state. `f = λx. g x`, `g = λx. f x` over
  `Dec → Dec`, but `g`'s body is left as `{:hole, "__pending__"}` (via `pending:
  [:g]`, honoured by `env_of`). At that moment `Certificate.mutual_group` reads
  `g`'s (hole) body, sees no onward callees, and collapses `f`'s SCC to a singleton
  — so a naive certifier certifies `f` as non-recursive though the `f↔g` cycle
  genuinely diverges (finding: premature totality certification). The certifier must
  DEFER (certify neither) while any callee is pending. `focus` is `[:f]` only (`g` is
  a placeholder, not a real def to judge). Label `:diverging`.

  The `diverging_mutual_pair` twin covers the FULL-env state (both bodies present);
  this covers the pending-sibling state, the only one that exposes the deferral path.
  """
  @spec diverging_pending_sibling() :: Challenge.t()
  def diverging_pending_sibling do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}
    bf = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :g}, {:var, 0}}}
    bg = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [%{name: :f, type: ty, body: bf}, %{name: :g, type: ty, body: bg}],
        pending: [:g],
        focus: [:f]
      },
      note: "diverging pair with sibling g still a pending placeholder (premature-cert guard)",
      cover_tag: :pending_sibling
    )
  end

  @doc """
  A genuinely structural-recursive total def: `h = λn. case n of {Z -> Z; S y -> h y}`
  over `Nat → Nat`. The self-call is on the `S`-branch-bound subterm, so the
  certifier accepts it correctly. Label `:terminating` — guards the eventual
  mutual-recursion fix against over-correction (umbrella §6).
  """
  @spec structural_terminating() :: Challenge.t()
  def structural_terminating do
    motive = {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :h}, {:var, 0}}}]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [%{name: :h, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: body}], focus: [:h]},
      note: "structural recursion h(S y) = h y",
      cover_tag: :structural
    )
  end

  @nat_mot {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}

  defp h_def(body, label, note, cell \\ nil) do
    Challenge.new(
      kind: :def_group,
      assay: "totality/#{label}",
      label: String.to_atom(label),
      payload: %{defs: [%{name: :h, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: body}], focus: [:h]},
      note: note,
      cover_tag: cell
    )
  end

  @doc """
  Structural recursion whose base (`Z`) branch carries a rich, call-free subterm —
  every non-application Core former the size-change walker descends through:
  the inductive `mk_pair` (`:ctor`) and ι-on-`:case` projections, the inductive
  `Equivalent`/`reflexive`/`:case`-transport (which replaced the retired
  `eq`/`refl`/`rewrite`), `pi`/`Sigma` (`:data`), and a
  variable-headed application. The lone self-call `h y` stays structural, so the def is certified;
  the enrichment exists purely to exercise `Certificate.walk_node`'s per-former arms.
  Label `:terminating`.
  """
  @spec enriched_terminating() :: Challenge.t()
  def enriched_terminating do
    st = {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}

    base =
      {:ctor, :mk_pair,
       [
         {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), st, @nat}, [{:mk_pair, 2, {:var, 1}}]},
         {:ctor, :mk_pair,
          [
            {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), st, @nat}, [{:mk_pair, 2, {:var, 0}}]},
            {:ctor, :mk_pair,
             [
               {:data, :Equivalent, [{:var, 0}], [{:var, 0}, {:var, 0}]},
               {:ctor, :mk_pair,
                [
                  {:ctor, :reflexive, [{:var, 0}]},
                  {:ctor, :mk_pair,
                   [
                     {:app,
                      {:case, {:ctor, :reflexive, [{:var, 0}]}, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}},
                       [{:reflexive, 1, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}}}]}, {:var, 0}},
                     {:ctor, :mk_pair,
                      [
                        {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat},
                        {:ctor, :mk_pair,
                         [
                           {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []},
                           {:app, {:var, 0}, {:var, 0}}
                         ]}
                      ]}
                   ]}
                ]}
             ]}
          ]}
       ]}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, @nat_mot, [{:Z, 0, base}, {:S, 1, {:app, {:global, :h}, {:var, 0}}}]}}

    h_def(body, "terminating", "structural recursion with a rich call-free base branch")
  end

  @doc """
  Structural recursion certified through an inner `:case` on a NON-variable
  scrutinee (`fst (pair y y)`), so `scrut_index` returns `nil` (no refinement from
  that match) yet the outer `S`-branch already exposed `y < n`, keeping `h y`
  structural. Label `:terminating`.
  """
  @spec nonvar_scrutinee_terminating() :: Challenge.t()
  def nonvar_scrutinee_terminating do
    inner =
      {:case,
       {:case, {:ctor, :mk_pair, [{:var, 0}, {:var, 0}]},
        {:lam, Cure.Core.Grade.unrestricted(),
         {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}, @nat},
        [{:mk_pair, 2, {:var, 1}}]}, @nat_mot, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :h}, {:var, 1}}}]}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, @nat_mot, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, inner}]}}

    h_def(body, "terminating", "certified through an inner case on a non-var scrutinee")
  end

  @doc """
  `h(S y) = h(S y)` — the self-call argument is syntactically the reconstruction of
  the matched scrutinee (`ctor(S, [y])`), so `arg_relation` yields `:equal`, never
  `:smaller`. Genuinely diverges (`h n → h n`). Label `:diverging` — exercises the
  ctor reconstruct-equal arm.
  """
  @spec reconstruct_equal_diverging() :: Challenge.t()
  def reconstruct_equal_diverging do
    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, @nat_mot,
        [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :h}, {:ctor, :S, [{:var, 0}]}}}]}}

    h_def(body, "diverging", "self-call arg is the scrutinee reconstruction (arg_relation :equal)", :reconstruct_equal)
  end

  @doc """
  `h(S y) = h(fst (pair n n))` — the self-call argument is a projection (neither a
  variable nor a constructor), so `arg_relation` falls through to `:unknown`. The
  argument is definitionally `n`, so it genuinely diverges. Label `:diverging` —
  exercises `arg_relation`'s catch-all arm.
  """
  @spec unknown_arg_diverging() :: Challenge.t()
  def unknown_arg_diverging do
    # in the S-branch the original scrutinee n sits at de Bruijn 1 (shifted past y)
    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, @nat_mot,
        [
          {:Z, 0, {:ctor, :Z, []}},
          {:S, 1,
           {:app, {:global, :h},
            {:case, {:ctor, :mk_pair, [{:var, 1}, {:var, 1}]},
             {:lam, Cure.Core.Grade.unrestricted(),
              {:data, :Sigma, [@nat, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}], []}, @nat},
             [{:mk_pair, 2, {:var, 1}}]}}}
        ]}}

    h_def(body, "diverging", "self-call arg is a projection → arg_relation :unknown")
  end

  @doc """
  Curried two-argument structural recursion `f a b = case b of {Z → Z; S y → f a y}`:
  the first parameter is preserved (`:equal`) while the second decreases
  (`:smaller`), so the change-matrix carries mixed relations and its transitive
  closure composes `:equal`·`:smaller` entries. Label `:terminating`.
  """
  @spec two_arg_terminating() :: Challenge.t()
  def two_arg_terminating do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat,
        {:case, {:var, 0}, @nat_mot,
         [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:app, {:global, :f}, {:var, 2}}, {:var, 0}}}]}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [%{name: :f, type: ty, body: body}], focus: [:f]},
      note: "curried 2-arg structural recursion f a (S y) = f a y (mixed change matrix)",
      cover_tag: :two_arg
    )
  end

  @doc """
  A genuinely-total MUTUAL pair `f(S y) = g y`, `g(S y) = f y` (both `Nat → Nat`,
  `Z` base) with `f`'s base branch calling an out-of-SCC total leaf `h = λx.x`.
  Each cross-call decreases, so the `{f, g}` group certifies — the counterpart to
  `diverging_mutual_pair` on the ACCEPT side, exercising the cross-function edge
  build + group closure (`function_edges` incl. its out-of-group emit arm,
  `mutual_group_total?`, `reaches?`, `callees_env`). Label `:terminating`.
  """
  @spec terminating_mutual_pair() :: Challenge.t()
  def terminating_mutual_pair do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}
    # f's Z-branch calls the out-of-group leaf h (identity) — an intra-body call to
    # a global NOT in the {f,g} SCC, so function_edges' emit takes its nil arm.
    bf =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, @nat_mot,
        [{:Z, 0, {:app, {:global, :h}, {:ctor, :Z, []}}}, {:S, 1, {:app, {:global, :g}, {:var, 0}}}]}}

    bg =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, @nat_mot, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :f}, {:var, 0}}}]}}

    bh = {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [
          %{name: :f, type: ty, body: bf},
          %{name: :g, type: ty, body: bg},
          %{name: :h, type: ty, body: bh}
        ],
        focus: [:f, :g]
      },
      note: "terminating mutual pair f(S y)=g y, g(S y)=f y; f base calls out-of-SCC leaf h",
      cover_tag: :mutual_accept
    )
  end

  @doc """
  Argument-swapping structural recursion `f a b = case a of {Z → Z; S y → f b y}`:
  a call-arg relates `:equal` to one column and `:smaller` to another, so the
  change-matrix's transitive closure composes an `:equal`·`:smaller` product
  (`pathmul(:equal, :smaller)`). Terminating (both descend over two steps). Label
  `:terminating`.
  """
  @spec swap_terminating() :: Challenge.t()
  def swap_terminating do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat,
        {:case, {:var, 1}, @nat_mot,
         [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:app, {:global, :f}, {:var, 1}}, {:var, 0}}}]}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [%{name: :f, type: ty, body: body}], focus: [:f]},
      note: "arg-swapping recursion f a b = f b y (equal·smaller matrix closure)"
    )
  end

  @doc """
  Nullary self-loop `f = f` (arity 0, body is the bare global): the change matrix
  is `0×0`, so the matrix builder's empty-dimension arm (`rows n<=0 → []`) fires.
  Genuinely diverges. Label `:diverging`.
  """
  @spec nullary_self_loop() :: Challenge.t()
  def nullary_self_loop do
    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{defs: [%{name: :f, type: @nat, body: {:global, :f}}], focus: [:f]},
      note: "nullary self-loop f = f (0×0 change matrix)",
      cover_tag: :nullary_self
    )
  end

  @doc """
  Nullary MUTUAL loop `f = g`, `g = f` (both arity 0): the cross-function edges are
  `0×0`, so their composition in the group closure exercises the empty-row matrix
  path (`row_len [] → 0`, `mat_compose` over empty rows). Genuinely diverges (the
  once-live mutual-cycle hole at nullary arity). Label `:diverging`.
  """
  @spec nullary_mutual_loop() :: Challenge.t()
  def nullary_mutual_loop do
    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [%{name: :f, type: @nat, body: {:global, :g}}, %{name: :g, type: @nat, body: {:global, :f}}],
        focus: [:f, :g]
      },
      note: "nullary mutual loop f = g, g = f (0×0 cross-function edges)",
      cover_tag: :nullary_mutual
    )
  end

  @doc """
  A non-total def whose non-decreasing self-call is hidden inside a `:case`-on-Bool
  branch: `f = λn:Int. case (n == 0) of {True -> 0; False -> f n}`. Diverges for
  every `n ≠ 0` (`f n → f n → …`). The self-call passes `n` unchanged, so it is not
  structurally decreasing. Label `:diverging`.

  This is the permanent regression guard for the Bool-eliminator totality hole (now
  a `:case` on the inductive Bool, retiring `bool_elim`): the structural certifier's
  `calls?`/`guarded_node?` traversals *must* descend into every `:case` branch. If
  they returned the catch-all `false`, the self-call would be invisible, `terminating?`
  would report a spurious `true`, and this loop would be certified total (a soundness
  infection). Kept forever.
  """
  @spec diverging_bool_elim_branch() :: Challenge.t()
  def diverging_bool_elim_branch do
    ty = {:pi, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), {:int_type},
       {:case, {:app, {:app, {:global, :int_eq}, {:var, 0}}, {:int_lit, 0}},
        {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bool, [], []}, {:int_type}},
        [{:True, 0, {:int_lit, 0}}, {:False, 0, {:app, {:global, :f}, {:var, 0}}}]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{defs: [%{name: :f, type: ty, body: body}], focus: [:f]},
      note: "self-call hidden in a :case-on-Bool branch (Bool-eliminator totality-hole guard)"
    )
  end

  @doc """
  A genuinely total structural recursion whose decreasing self-call sits *inside*
  a `:case`-on-Bool branch: `h = λn:Nat. case n of {Z -> Z; S y -> case True of
  {True -> h y; False -> h y}}`. Each self-call passes `y`, the `S`-branch-bound
  subterm, so it is structurally smaller. Label `:terminating`.

  Companion to `diverging_bool_elim_branch/0`: it guards against the certifier
  *over*-correcting — `guarded_node?`'s `:case` clause must *recurse* into the
  branches carrying the current `root`/`smaller` (for Bool's arity-0 ctors,
  unchanged), not blanket-reject (or blanket-accept) a term that contains one.
  """
  @spec terminating_bool_elim_branch() :: Challenge.t()
  def terminating_bool_elim_branch do
    inner =
      {:case, {:ctor, :True, []}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bool, [], []}, @nat},
       [{:True, 0, {:app, {:global, :h}, {:var, 0}}}, {:False, 0, {:app, {:global, :h}, {:var, 0}}}]}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat},
        [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, inner}]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{defs: [%{name: :h, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: body}], focus: [:h]},
      note: "structural recursion with the decreasing self-call inside a bool_elim branch"
    )
  end

  # -- W1: adversarial diverging set (pre-port banking spec §4 W1) ------------
  # Each is diverging BY CONSTRUCTION (argument in @doc). All are rejected by
  # today's conservative certifier (mutual cycles rejected wholesale; the
  # self-call variants fail the fixed-position structural guard) — and must
  # STAY rejected forever, including after the P1 size-change port.

  @doc """
  Diverging 3-cycle `f → g → h → f` over `Dec → Dec`. No body references its own
  name; only signature-level cycle detection sees it (generalizes the banked
  2-cycle). Diverges on every input: `f x → g x → h x → f x → …`. Label `:diverging`.
  """
  @spec diverging_three_cycle() :: Challenge.t()
  def diverging_three_cycle do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}
    bf = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :g}, {:var, 0}}}
    bg = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :h}, {:var, 0}}}
    bh = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{name: :f, type: ty, body: bf},
          %{name: :g, type: ty, body: bg},
          %{name: :h, type: ty, body: bh}
        ],
        focus: [:f, :g, :h]
      },
      note: "W1 3-cycle f->g->h->f; every body self-call-free"
    )
  end

  @doc """
  Diverging cycle whose every direct callee looks innocent: `f = λx. total_id (g x)`,
  `g = λx. f x`, with `total_id = λx. x` genuinely total. The cycle f→g→f exists but
  is interleaved with a plain subroutine call. `total_id` is deliberately NOT in
  `focus` — it must keep certifying (asserted separately). Diverges on every input.
  Label `:diverging`.
  """
  @spec diverging_mediated_cycle() :: Challenge.t()
  def diverging_mediated_cycle do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}
    b_id = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:var, 0}}
    bf = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :total_id}, {:app, {:global, :g}, {:var, 0}}}}
    bg = {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:global, :f}, {:var, 0}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{name: :total_id, type: ty, body: b_id},
          %{name: :f, type: ty, body: bf},
          %{name: :g, type: ty, body: bg}
        ],
        focus: [:f, :g]
      },
      note: "W1 cycle f->g->f mediated by a total helper (total_id excluded from focus)"
    )
  end

  @doc """
  Argument-permuting, size-preserving mutual pair over `Dec → Dec → Dec`:
  `f x y = g y x`, `g x y = f x y`. Every argument-to-argument flow is `≤`, none
  is `<` — the classic size-change discriminator: a naive "some argument shrinks
  somewhere" analysis wrongly certifies it, LJB composition does not. Diverges on
  every input pair. Label `:diverging`.
  """
  @spec diverging_permuting_pair() :: Challenge.t()
  def diverging_permuting_pair do
    ty = {:pi, Cure.Core.Grade.unrestricted(), @dec, {:pi, Cure.Core.Grade.unrestricted(), @dec, @dec}}
    # inner frame: y = var 0, x = var 1
    bf =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:app, {:global, :g}, {:var, 0}}, {:var, 1}}}}

    bg =
      {:lam, Cure.Core.Grade.unrestricted(), @dec,
       {:lam, Cure.Core.Grade.unrestricted(), @dec, {:app, {:app, {:global, :f}, {:var, 1}}, {:var, 0}}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [%{name: :f, type: ty, body: bf}, %{name: :g, type: ty, body: bg}],
        focus: [:f, :g]
      },
      note: "W1 permuting pair f x y = g y x; g x y = f x y — all flows ≤, none <"
    )
  end

  @doc """
  Constructor-regrowing self-call: `h = λn. case n of {Z -> Z; S y -> h (S y)}`
  over `Nat → Nat`. The self-call re-wraps the just-unpacked field, so descent is
  claimed by shape and refuted by size: `h (S m) → h (S m) → …` diverges on every
  `S`-input. Label `:diverging`.
  """
  @spec diverging_regrowing_self() :: Challenge.t()
  def diverging_regrowing_self do
    motive = {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}

    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, motive,
        [
          {:Z, 0, {:ctor, :Z, []}},
          {:S, 1, {:app, {:global, :h}, {:ctor, :S, [{:var, 0}]}}}
        ]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{defs: [%{name: :h, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: body}], focus: [:h]},
      note: "W1 regrowing self-call h (S y) — diverges on every S input"
    )
  end

  @doc """
  One-leg-decreasing mutual pair: `f = λn. case n of {Z -> Z; S y -> g y}` and
  `g = λn. f (S n)` over `Nat → Nat`. The f→g call strictly decreases; the g→f
  call regrows; the COMPOSED cycle is non-decreasing: `f (S m) → g m → f (S m) → …`.
  LJB's motivating case — certification must consider cycle composition, not
  individual calls. Label `:diverging`.
  """
  @spec diverging_one_leg_pair() :: Challenge.t()
  def diverging_one_leg_pair do
    motive = {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}

    bf =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :g}, {:var, 0}}}]}}

    bg = {:lam, Cure.Core.Grade.unrestricted(), @nat, {:app, {:global, :f}, {:ctor, :S, [{:var, 0}]}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{name: :f, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: bf},
          %{name: :g, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: bg}
        ],
        focus: [:f, :g]
      },
      note: "W1 one-leg pair: f decreases, g regrows; composed cycle non-decreasing"
    )
  end

  # -- W2: reach pins (pre-port banking spec §4 W2) ----------------------------
  # Ground-truth :terminating (argument in each @doc), conservatively rejected by
  # today's certifier (mutual groups rejected wholesale; multi-argument descent
  # fails the fixed-position guard). Banked in test/antigen/reach.sexp, NOT
  # corpus.sexp; P1 migrates them. Labels are truth, not checker behavior (D3).

  @doc """
  Well-founded structural mutual pair: `even = λn. case n of {Z -> Z; S y -> odd y}`,
  `odd = λn. case n of {Z -> S Z; S y -> even y}` over `Nat → Nat` (Nat-valued to
  stay in one family). Every cross-call passes the strict predecessor, so the
  composed cycle strictly decreases: total. Label `:terminating` — rejected today
  only because the certifier rejects all mutual cycles.
  """
  @spec wellfounded_even_odd() :: Challenge.t()
  def wellfounded_even_odd do
    motive = {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}

    be =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:app, {:global, :odd}, {:var, 0}}}]}}

    bo =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:case, {:var, 0}, motive,
        [
          {:Z, 0, {:ctor, :S, [{:ctor, :Z, []}]}},
          {:S, 1, {:app, {:global, :even}, {:var, 0}}}
        ]}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [
          %{name: :even, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: be},
          %{name: :odd, type: {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body: bo}
        ],
        focus: [:even, :odd]
      },
      note: "W2 reach pin: well-founded mutual even/odd (P1 target)"
    )
  end

  @doc """
  Ackermann over `Nat → Nat → Nat`:
  `ack Z n = S n; ack (S m') Z = ack m' (S Z); ack (S m') (S n') = ack m' (ack (S m') n')`.
  Total by the lexicographic measure (m, n): every call either decreases m, or
  keeps m and decreases n. Rejected today: no SINGLE fixed argument position
  decreases at every self-call (the inner call's first argument is `S m'`, a
  constructor, not a bound variable). Label `:terminating`.
  """
  @spec wellfounded_ackermann() :: Challenge.t()
  def wellfounded_ackermann do
    motive = {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}

    # frame under λm. λn.: m = var 1, n = var 0
    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat,
        {:case, {:var, 1}, motive,
         [
           # Z: S n
           {:Z, 0, {:ctor, :S, [{:var, 0}]}},
           # S m' (binds m' at 0; n shifts to 1, m to 2)
           {:S, 1,
            {:case, {:var, 1}, motive,
             [
               # n = Z: ack m' (S Z)
               {:Z, 0, {:app, {:app, {:global, :ack}, {:var, 0}}, {:ctor, :S, [{:ctor, :Z, []}]}}},
               # n = S n' (binds n' at 0; m' shifts to 1): ack m' (ack (S m') n')
               {:S, 1,
                {:app, {:app, {:global, :ack}, {:var, 1}},
                 {:app, {:app, {:global, :ack}, {:ctor, :S, [{:var, 1}]}}, {:var, 0}}}}
             ]}}
         ]}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [
          %{
            name: :ack,
            type: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}},
            body: body
          }
        ],
        focus: [:ack]
      },
      note: "W2 reach pin: Ackermann, lexicographic (m, n) descent (P1 target)"
    )
  end

  @doc """
  Permuted well-founded pair over `Nat`: `f = λn. λm. case n of {Z -> m; S y -> g m y}`
  and `g = λa. λb. f b a`. Descent is visible only by tracking arguments across the
  swap: `f (S y) m → g m y → f y m` — f's first argument strictly decreases every
  round trip. Total; rejected today as a mutual cycle. The accept-side twin of W1's
  `diverging_permuting_pair`. Label `:terminating`.
  """
  @spec wellfounded_permuted_pair() :: Challenge.t()
  def wellfounded_permuted_pair do
    motive = {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}

    # f frame: n = var 1, m = var 0; S-branch binds y at 0 (m -> 1, n -> 2)
    bf =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat,
        {:case, {:var, 1}, motive,
         [
           {:Z, 0, {:var, 0}},
           {:S, 1, {:app, {:app, {:global, :g}, {:var, 1}}, {:var, 0}}}
         ]}}}

    # g a b = f b a; frame: a = var 1, b = var 0
    bg =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat, {:app, {:app, {:global, :f}, {:var, 0}}, {:var, 1}}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/terminating",
      label: :terminating,
      payload: %{
        defs: [
          %{
            name: :f,
            type: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}},
            body: bf
          },
          %{
            name: :g,
            type: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}},
            body: bg
          }
        ],
        focus: [:f, :g]
      },
      note: "W2 reach pin: descent visible only across the argument swap (P1 target)"
    )
  end

  @doc """
  Single-function, multi-argument diverging control over `Nat → Nat → Nat`:
  `loop a b = loop (S a) (S b)`. Both parameters are UNMATCHED (no `case`), so
  the size-change analysis has no smaller-set and no matched-pattern form to
  reconstruct against — every call-arc is `:unknown`, the sole idempotent loop
  has no `:smaller` diagonal, and the def is (soundly) rejected. This is the
  single-function multi-arg twin of W1's mutual `diverging_permuting_pair`, and
  the direct falsifier for the #14 reconstruct-equal machinery: reconstruct-equal
  must NOT fire on unmatched parameters (`S a` / `S b` are regrown constructors,
  not reconstructions of any matched form). Label `:diverging`.
  """
  @spec diverging_size_change_control() :: Challenge.t()
  def diverging_size_change_control do
    # frame under λa. λb.: a = var 1, b = var 0
    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat,
        {:app, {:app, {:global, :loop}, {:ctor, :S, [{:var, 1}]}}, {:ctor, :S, [{:var, 0}]}}}}

    Challenge.new(
      kind: :def_group,
      assay: "totality/diverging",
      label: :diverging,
      payload: %{
        defs: [
          %{
            name: :loop,
            type: {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}},
            body: body
          }
        ],
        focus: [:loop]
      },
      note: "size-change control: loop a b = loop (S a) (S b) — unmatched params, all-unknown loop"
    )
  end

  @doc """
  Rebuild the def-group's `Env` by folding `Env.add_def/4` over the payload.
  Seeded with the builtin-op globals first (K2, spec 2026-07-09): the catalog's
  retargeted `int_eq` spine (diverging_bool_elim_branch) must not die
  `:unknown_global` when a consumer resolves the group's globals.

  A def named in `payload.pending` is registered with the elaborator's
  `{:hole, "__pending__"}` placeholder body instead of its real body — reproducing
  the mid-body_pass state in which a sibling has a signature but no elaborated term
  (see `diverging_pending_sibling/0`).
  """
  @spec env_of(Challenge.t()) :: Env.t()
  def env_of(%Challenge{payload: %{defs: defs} = payload}) do
    pending = Map.get(payload, :pending, [])

    Enum.reduce(defs, Cure.Core.Builtins.seed_ops(Env.empty()), fn d, env ->
      body = if d.name in pending, do: {:hole, "__pending__"}, else: d.body
      Env.add_def(env, d.name, d.type, body)
    end)
  end
end
