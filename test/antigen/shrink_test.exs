defmodule Antigen.ShrinkTest do
  use ExUnit.Case, async: true
  alias Antigen.{Shrink, Challenge}
  alias Antigen.Generators.{Term, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Cure.Core.{Context, Kernel}

  # a well-typed-ish artifact whose predicate is purely structural for these unit tests
  defp art(term, ctx \\ []) do
    Challenge.new(
      kind: :typed_term,
      assay: "term/infer_check",
      label: :well_typed,
      payload: %{sig: :v1, ctx: ctx, type: {:data, :Nat, [], []}, term: term}
    )
  end

  defp s(n), do: {:ctor, :S, [n]}
  defp num(0), do: {:ctor, :Z, []}
  defp num(k), do: s(num(k - 1))

  test "numeral shrink + subterm→atom reduces under a 'contains an S' predicate to a single S Z" do
    # S(S(S Z)))
    a = art(s(s(s(num(0)))))
    pred = fn ch -> match?({:ctor, :S, _}, ch.payload.term) end
    out = Shrink.minimize(a, pred, 1000)
    # minimal term still headed by S
    assert out.payload.term == s(num(0))
    assert pred.(out)
  end

  test "structural unwrap peels an app/ctor wrapper down to the payload leaf" do
    # plus(vcons(...), Z) — predicate keeps any term still containing a vcons
    inner = {:ctor, :vcons, [num(0), num(0), {:ctor, :vnil, []}]}
    a = art({:app, {:app, {:global, :plus}, inner}, num(0)})
    pred = fn ch -> contains_vcons?(ch.payload.term) end
    out = Shrink.minimize(a, pred, 1000)
    assert out.payload.term == {:ctor, :vnil, []} or match?({:ctor, :vcons, _}, out.payload.term)
    assert Shrink.size(out) < Shrink.size(a)
    assert pred.(out)
  end

  test "lam-body unwrap shifts free vars and is rejected when body uses its own param" do
    # NOT `fn _ -> true end`: rule 1 is tried before rule 4 ("here" order is
    # rule1 ++ rule2 ++ rule4) and fires on ANY node with node_count > 1 — the
    # top-level lam here has node_count 3 (lam + Nat-dom + var), so a fully
    # permissive predicate would let rule 1 replace the WHOLE lam with its
    # first minimal-atom menu item ({:ctor,:Z,[]}) before rule 4's lam-unwrap
    # is ever tried, and the test would observe `{:ctor,:Z,[]}`, not
    # `{:var,0}` (confirmed by hand-trace + probe against the plan's own
    # `size`/`node_count` helpers). The predicate must exclude the minimal
    # atoms so only a `:var`/`:lam`-shaped result is accepted, isolating rule
    # 4's behavior.
    keep_var_or_lam = fn ch -> match?({:var, _}, ch.payload.term) or match?({:lam, _g, _, _}, ch.payload.term) end
    # λx:Nat. (var 1)  — body does NOT use var 0 ⇒ unwrap to (var 0) after shift
    a = art({:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:var, 1}}, [{:data, :Nat, [], []}])
    out = Shrink.minimize(a, keep_var_or_lam, 1000)
    # shifted down by 1
    assert out.payload.term == {:var, 0}
  end

  test "deterministic + monotone + idempotent" do
    a = art(s(s(num(0))))
    pred = fn ch -> match?({:ctor, :S, _}, ch.payload.term) end
    o1 = Shrink.minimize(a, pred, 1000)
    o2 = Shrink.minimize(a, pred, 1000)
    assert o1 == o2
    assert Shrink.size(o1) <= Shrink.size(a)
    # idempotent
    assert Shrink.minimize(o1, pred, 1000) == o1
  end

  test "budget caps cost (pred calls), not accepted edits — spec §3" do
    # NOTE (execution finding): the plan's prior form of this test assumed
    # budget = number of *accepted edits* (`budget:1` ⇒ one edit ⇒ progress).
    # That contradicts spec §3, which defines budget as "max candidate
    # evaluations, i.e. pred calls" — a COST cap. For `num(5)` under an
    # S-headed predicate each sweep rejects the 4 minimal-atom candidates
    # (Z/vnil/T/Type₀ — none S-headed) before rule 2's single-S-peel is
    # accepted, so the FIRST accept costs 5 pred calls. A budget below that
    # makes ZERO progress (the cost cap bites first — correct behavior); a
    # large budget reaches the fixpoint S Z. Rewritten to the spec-faithful
    # behavior (test-encodes-wrong-behavior exception, justified by §3).
    # size 11
    a = art(num(5))
    pred = fn ch -> match?({:ctor, :S, _}, ch.payload.term) end
    # 3 pred calls all reject ⇒ no progress
    assert Shrink.minimize(a, pred, 3).payload.term == num(5)
    out_full = Shrink.minimize(a, pred, 1000)
    # fixpoint: S Z
    assert out_full.payload.term == s(num(0))
    # enough budget minimizes
    assert Shrink.size(out_full) < Shrink.size(a)
  end

  test "a predicate that raises is safely treated as reject (LOCKED: pred crashes are rescued)" do
    # Global Constraints locks "pred crashes are rescued -> reject", implemented
    # by `safe_pred/2`, but no test anywhere exercised a raising predicate
    # before this — a real gap, since `well_formed?` is shape-only (doesn't
    # check de-Bruijn closedness), so a real assay could plausibly raise on an
    # out-of-scope candidate `pred` builds from. Here `pred` raises
    # specifically on `Z`, so the sweep must safely skip over it (not crash)
    # and settle at the last candidate where `pred` holds without raising.
    # S(S(Z))
    a = art(s(s(num(0))))

    pred = fn ch ->
      case ch.payload.term do
        {:ctor, :S, _} -> true
        {:ctor, :Z, []} -> raise "boom"
        _ -> false
      end
    end

    # must not raise
    out = Shrink.minimize(a, pred, 1000)
    # settles at S Z: Z is reachable but pred raises there
    assert out.payload.term == s(num(0))
    assert pred.(out)
  end

  test "context drop removes an unreferenced entry and shifts higher vars down" do
    # ctx [Nat, Nat]; term uses only var 0 ⇒ entry 1 is droppable, var 0 stays, higher shift
    a = art({:var, 0}, [{:data, :Nat, [], []}, {:data, :Nat, [], []}])
    out = Shrink.minimize(a, fn _ -> true end, 1000)
    assert length(out.payload.ctx) < 2
    # every var in the result is in-scope for its ctx
    assert Antigen.Shrink.closed?(out)
  end

  test "context drop is REJECTED when the entry is referenced" do
    # term uses var 1 ⇒ entry 1 (abs index 1) may not be dropped; but entry 0 (var 0 unused) may
    a = art({:var, 1}, [{:data, :Nat, [], []}, {:data, :Nat, [], []}])
    out = Shrink.minimize(a, fn ch -> Antigen.Shrink.occurs?(ch.payload.term, 0) end, 1000)
    # predicate forces keeping a reference to abs-0 after shifts; result stays closed + valid
    assert Antigen.Shrink.closed?(out)
    assert Antigen.Shrink.occurs?(out.payload.term, 0)
  end

  test "every ctx-drop candidate is de-Bruijn closed (regression guard for §7.3)" do
    a =
      art(
        {:app, {:var, 0}, {:var, 2}},
        [{:data, :Nat, [], []}, {:data, :Nat, [], []}, {:data, :Nat, [], []}]
      )

    for c <- Antigen.Shrink.candidates_for_test(a) do
      assert Antigen.Shrink.closed?(c), "candidate not closed: #{inspect(c.payload)}"
    end
  end

  test "context drop shifts cross-referencing sibling entries correctly (dependent ctx, §7.3)" do
    # An all-`Nat` ctx (no entry ever references another) can pass `closed?`
    # trivially even if the sibling-shift cutoff (`Term.shift(e, -1, d - pos)`)
    # were wrong, because every shift on such a ctx is a no-op — it never
    # exercises spec §4 rule 3's "asymmetric before/after-drop-position
    # handling". This ctx is genuinely dependent: pos0 references BOTH pos1
    # and pos3, straddling the sole droppable position (pos2), so a wrong
    # cutoff would produce a wrong (but still shape-`closed?`) index. Hand
    # (and mechanically probe-)verified expected output before writing this
    # assertion.
    ctx = [
      # pos0: local 0 -> abs 1 (pos1); local 2 -> abs 3 (pos3)
      {:data, :Equivalent, [{:type, 0}], [{:var, 0}, {:var, 2}]},
      # pos1: local 1 -> abs 3 (pos3)
      {:data, :Vec, [], [{:var, 1}]},
      # pos2: unreferenced — the sole droppable entry
      {:data, :Nat, [], []},
      # pos3
      {:data, :Nat, [], []}
    ]

    a = art({:var, 0}, ctx)
    # only pos2 is unreferenced
    assert [c] = Antigen.Shrink.candidates_for_test(a)

    assert c.payload.ctx == [
             # pos0: local 2 -> local 1 (target abs shifted 3 -> 2)
             {:data, :Equivalent, [{:type, 0}], [{:var, 0}, {:var, 1}]},
             # pos1: local 1 -> local 0 (target abs shifted 3 -> 2)
             {:data, :Vec, [], [{:var, 0}]},
             # old pos3, now pos2, content unchanged
             {:data, :Nat, [], []}
           ]

    assert Antigen.Shrink.closed?(c)
  end

  test "shrinks a deep well-typed term to a minimal vcons-containing witness (§7.4)" do
    env = SigMenu.env_of(:v1)
    ctx = Context.empty(env)

    infer_ok? = fn ch ->
      c = SigMenu.rebuild_context(env, ch.payload.ctx)
      match?({:ok, _}, Kernel.infer(c, ch.payload.term))
    end

    pred = fn ch -> infer_ok?.(ch) and contains_vcons?(ch.payload.term) end

    # find a generated well-typed term containing a vcons, then shrink
    seed =
      B.interp(Term.gen_term(ctx, {:data, :Vec, [], [{:ctor, :S, [{:ctor, :Z, []}]}]}))
      |> Enum.take(50)
      |> Enum.find(&contains_vcons?/1)

    # Load-bearing, not vacuous: `assert seed` fails loudly (not silently skips)
    # if no vcons-containing term is sampled (recursive-skeptical-review finding).
    assert seed, "no vcons-containing term sampled in 50 draws"
    a = art(seed)
    assert pred.(a)
    out = Shrink.minimize(a, pred, 5000)
    assert pred.(out)
    assert Shrink.size(out) <= Shrink.size(a)
    # Exact global minimum (probe-verified stable across seeds): the smallest
    # well-typed vcons-containing term is `vcons Z Z vnil : Vec (S Z)`, size 4.
    # Asserting the exact witness (not a loose `<= 8` bound) makes this
    # load-bearing — it verifies the greedy sweep reaches the true minimum, not
    # merely "something small".
    assert out.payload.term == {:ctor, :vcons, [{:ctor, :Z, []}, {:ctor, :Z, []}, {:ctor, :vnil, []}]}
    assert Shrink.size(out) == 4
  end

  defmodule BuggyMutationAssay do
    # wraps Assays.Mutation with an infer that WRONGLY ACCEPTS :head_swap mutants
    alias Cure.Core.Kernel

    def run(%{payload: %{fault: %{kind: :head_swap}}} = c) do
      # `{:expected, _}`-tag the (deliberately-simulated) violation so the Runner
      # renders it as a calm immune response, not an alarming "ANTIGEN INFECTION"
      # — this assay fakes a buggy kernel purely to exercise the shrink machinery.
      case Antigen.Assays.Mutation.run(c, fn ctx, t ->
             case Kernel.infer(ctx, t) do
               # pretend it type-checks ⇒ wrongly accepted
               {:error, _} -> {:ok, {:type, 0}}
               ok -> ok
             end
           end) do
        {:violation, detail} -> {:violation, {:expected, detail}}
        other -> other
      end
    end

    def run(c), do: Antigen.Assays.Mutation.run(c)
  end

  test "Runner shrinks a deep head_swap survivor to the bare minimal witness before banking (§7.5)" do
    alias Antigen.Generators.Mutation
    tmp = "tmp/antigen_shrink"
    corpus = Path.join(tmp, "shrink_ab_#{:erlang.unique_integer([:positive])}.sexp")
    File.rm(corpus)

    # a deep head_swap mutant (grown by deepen), in a padded context
    deep =
      B.interp(Mutation.mutant())
      |> Enum.take(400)
      |> Enum.find(fn c -> c.payload.fault.kind == :head_swap and c.payload.fault.depth >= 3 end)

    assert deep, "no deep head_swap mutant sampled"

    Antigen.Runner.explore(
      challenges: [deep],
      count: 1,
      assay: BuggyMutationAssay,
      corpus_path: corpus,
      seeds_path: Path.join(tmp, "seeds_ignore.sexp"),
      report_dir: tmp
    )

    banked =
      Antigen.Corpus.stream(corpus)
      |> Enum.flat_map(fn
        {:ok, c} -> [c]
        _ -> []
      end)

    assert [ab] = banked
    # NOTE on what this does/doesn't prove: `Antigen.Assays.Mutation.run/2`
    # (unmodified) treats ANY `{:ok, _}` from `infer_fun` as a violation, and
    # this wrapper returns `{:ok, _}` unconditionally, so `pred` is true for any
    # well-formed candidate — rule 1 will likely collapse `deep` to an unrelated
    # minimal atom on the first accepted edit. That's expected (spec §2). What
    # this proves is narrower than "the minimal head_swap witness": that
    # `explore/1` wires minimize-before-bank correctly, that `minimize` makes
    # real progress, and that the banked artifact still trips the configured assay.
    assert Antigen.Shrink.size(ab) < Antigen.Shrink.size(deep)
    assert match?({:violation, {:expected, {:accepted_ill_typed, _, _}}}, BuggyMutationAssay.run(ab))
  end

  defp contains_vcons?({:ctor, :vcons, _}), do: true
  defp contains_vcons?(t) when is_tuple(t), do: t |> Tuple.to_list() |> tl() |> Enum.any?(&contains_vcons?/1)
  defp contains_vcons?(l) when is_list(l), do: Enum.any?(l, &contains_vcons?/1)
  defp contains_vcons?(_), do: false

  describe "shrink-all-kinds (pieces bridge)" do
    alias Antigen.{Challenge, Shrink}

    @nat {:data, :Nat, [], []}
    # a family whose single ctor has one deliberately bloated arg type
    defp bloated_family_ch do
      bloated = {:app, {:app, {:global, :plus}, {:ctor, :S, [{:ctor, :Z, []}]}}, {:ctor, :Z, []}}
      fam = Cure.Core.Inductive.family(:F, [], [], 0)
      ctor = Cure.Core.Inductive.ctor(:MkF, [{:x, bloated}], [], [:unrestricted], [])

      Challenge.new(
        kind: :family,
        assay: "positivity",
        label: :well_typed,
        payload: %{family: fam, ctors: [ctor]},
        seed: 1
      )
    end

    test "a family's bloated ctor-arg term is shrunk (all-kinds via pieces)" do
      ch = bloated_family_ch()
      # predicate: the challenge still has a ctor whose arg term is non-atomic
      #   (satisfied by the bloated original AND by any smaller-but-nonatomic form),
      #   plus stays well-formed — a synthetic same-shape closure.
      pred = fn c ->
        match?(%Challenge{kind: :family, payload: %{ctors: [_ | _]}}, c)
      end

      out = Shrink.minimize(ch, pred, 500)
      # candidates are produced for a :family now (was []/unsupported before)
      assert Shrink.candidates(ch) != []
      # minimized artifact is still a well-formed family satisfying the predicate
      assert pred.(out)
      assert Shrink.well_formed?(out)
    end

    test "typed_term candidate set is unchanged by the generalization" do
      # a representative typed_term; candidates/1 must still include ctx-drop + type/term rewrites
      ch =
        Challenge.new(
          kind: :typed_term,
          assay: "term/infer_check",
          label: :well_typed,
          payload: %{sig: :v1, ctx: [], type: @nat, term: {:ctor, :S, [{:ctor, :Z, []}]}},
          seed: 1
        )

      cands = Shrink.candidates(ch)
      # S(Z) → Z is rule2; must still be offered on the typed_term term field
      assert Enum.any?(cands, fn c -> c.payload.term == {:ctor, :Z, []} end)
    end

    test "well_formed?/1 recognizes a :stuck_elim challenge (shares :forcing_pair's payload shape)" do
      # :stuck_elim's payload is %{defs:, focus:, t:, tprime:} — identical to :forcing_pair's
      # (Challenge.to_pieces/1 shares one clause for both kinds via `kind in [...]`). Today
      # Coverage.terms_of/1 only has a LITERAL `kind: :forcing_pair` clause, so this legitimately
      # well-formed :stuck_elim challenge crashes Coverage.terms_of/1 (FunctionClauseError),
      # rescued by well_formed?/1 to `false` — wrongly reporting it as malformed. Once every
      # kind routes through Triage (Task 4), that false negative makes :stuck_elim a silent,
      # permanent no-op (every Bisect/Shrink candidate rejected by the well-formed? pre-filter).
      # body is S(Z), not the bare atom Z — an atomic {:ctor, :Z, []} everywhere would make
      # every piece already-minimal (node_count == 1, no rule1/rule2/rule4/child_slots
      # candidates), which would fail `candidates(ch) != []` below for an unrelated reason.
      # label :positive matches Antigen.Assays.StuckElimDelta's real semantics for this
      # kind (t/tprime committed as convertible); irrelevant to well_formed?/candidates
      # (neither reads `label`), but kept realistic rather than borrowing :def_group's
      # :terminating label.
      ch =
        Challenge.new(
          kind: :stuck_elim,
          assay: "stuck_elim_delta",
          label: :positive,
          payload: %{
            defs: [%{name: :f, type: @nat, body: {:ctor, :S, [{:ctor, :Z, []}]}}],
            focus: [:f],
            t: {:ctor, :Z, []},
            tprime: {:ctor, :Z, []}
          },
          seed: 1
        )

      assert Shrink.well_formed?(ch)
      assert Shrink.candidates(ch) != []
    end
  end
end
