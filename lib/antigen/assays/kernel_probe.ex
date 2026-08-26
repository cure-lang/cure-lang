defmodule Antigen.Assays.KernelProbe do
  @moduledoc """
  `kernel/probe` — a coverage-completion vertical for the kernel's def-level and
  inference-mode *defensive* clauses that no term-shaped generator reaches, because
  they are entry points into `check_def`/`validate_certificate`/`check_family`/
  `normalize/3` (not `infer` of a single closed term) or `infer` rejections gated
  out of the live campaign by the runner's `well_formed?` filter.

  Each probe is a real soundness assertion — the kernel MUST return the documented
  verdict for the deliberately-shaped input (reject the ill-typed term, certify the
  body-less builtin op, reject the over-ceiling family, pass the field error through
  the non-family `remap_index_error` clause, …). A wrong verdict is an infection.

  Oracle = the fixed expected outcome per probe (`expected/1`); the payload carries
  only the probe tag, so `Coverage.terms_of` returns `[]` and the challenge bypasses
  the term-well-formedness gate (like `check/verdict`, `serialize/decode`).
  """
  alias Antigen.Challenge

  alias Cure.Core.{
    Kernel,
    Builtins,
    Env,
    Context,
    Eval,
    Conv,
    Inductive,
    Universe,
    Normalise,
    Quote,
    Serialize,
    Validator
  }

  alias Cure.Migrate.Rule
  alias Cure.Compiler.{Lexer, Parser, Trivia}

  @nat {:data, :Nat, [], []}
  @z {:ctor, :Z, []}
  @bounded_ty {:data, :Bounded, [], []}

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :kernel_probe, payload: %{probe: probe}}) do
    got = evaluate(probe)

    if matches?(probe, got) do
      :ok
    else
      {:violation, {:kernel_probe_wrong_verdict, probe, got}}
    end
  end

  # -- the base env: canonical families (Bool/Nat/Eq/Sigma/List) + 25 builtin-ops --
  defp base_env, do: Builtins.seed(Env.empty())

  # `Builtins.seed/1` does NOT register the compact-`Bounded` builtin family, so any
  # `infer`/`check` of a `{:bounded_lit, _}` that needs the family requires an env
  # that declares `Bounded(n)` and marks it the `:bounded` builtin.
  defp bounded_env do
    base_env()
    |> Inductive.declare(Inductive.family(:Bounded, [], [{:n, @nat}], 0), [])
    |> Inductive.register_builtin(:bounded, :Bounded)
  end

  defp bounded_ctx, do: Context.empty(bounded_env())

  # The public door to the private index-unifier: `branch_unify/5` on a one-ctor
  # family whose declared result-index we choose (`ridx`), unified against a
  # scrutinee index list (`scrut`). Returns `:trivial` / `:impossible`.
  defp unify_index(ridx, scrut) do
    fam =
      Inductive.declare(base_env(), Inductive.family(:BF, [], [{:n, @nat}], 0), [
        Inductive.ctor(:bc, [], ridx, [], [])
      ])

    Kernel.branch_unify(Context.empty(fam), :BF, :bc, scrut, [])
  end

  # Size-change certification of a self-referential `:f` whose body is the (possibly
  # malformed) `body`. Registers `:f` so the call graph is realistic.
  defp cert_terminates?(body) do
    env = Env.add_def(base_env(), :f, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body)
    Cure.Elab.TotalityClosure.provably_total?(env, :f)
  end

  # -- per-probe kernel invocation (returns the raw kernel result) --
  defp evaluate(:infer_absurd), do: Kernel.infer(ctx(), {:absurd})
  defp evaluate(:infer_fields_only_ctor), do: Kernel.infer(ctx(), {:ctor, :mk_pair, [@z, @z]})
  defp evaluate(:check_ctor_arity), do: Kernel.check(ctx(), {:ctor, :S, [@z, @z]}, Eval.eval(@nat, []))
  defp evaluate(:check_def_unknown), do: Kernel.check_def(base_env(), :nosuchdef)
  defp evaluate(:check_def_builtin_op), do: Kernel.check_def(base_env(), :int_add)
  defp evaluate(:validate_cert_builtin_op), do: Kernel.validate_builtin_certificate(base_env(), :int_add)

  defp evaluate(:family_ceiling) do
    fam = Inductive.family(:TooHigh, [], [], Universe.ceiling() + 1)
    Kernel.check_family(base_env(), fam)
  end

  defp evaluate(:normalize_opts), do: Kernel.normalize(ctx(), {:nat_lit, 3}, [])

  # A def whose body is a hole: `check` admits a hole against any type (K3), so
  # check_def succeeds, but the Final-Core validator's `no_hole: :warn` clause
  # produces a warning — driving the warning-emit fold in `run_final_core_validator`.
  defp evaluate(:validator_warn_emit) do
    env = Env.add_def(base_env(), :holey, @nat, {:hole, :h})
    Kernel.check_def(env, :holey)
  end

  # A constructor field whose expected type is a NON-family value (`Int`), checked
  # against a mismatching term: `remap_index_error` must PASS THE ERROR THROUGH
  # (the `:index_mismatch` remap fires only when the expected type is a `:vdata`).
  defp evaluate(:remap_index_passthrough) do
    fam = Inductive.family(:Wrap, [], [], 0)
    ctor = Inductive.ctor(:wrap, [{:v, {:int_type}}], [], [:unrestricted], [])
    env = Inductive.declare(base_env(), fam, [ctor])
    Kernel.check(Context.empty(env), {:ctor, :wrap, [{:type, 0}]}, {:vdata, :Wrap, []})
  end

  # `Quote.reify` of a data value whose family is ABSENT from the (non-nil) sig:
  # `split_data_args`'s family-not-found fallback treats every arg as a param
  # rather than crashing (defensive — a value reified against a foreign/partial
  # signature). The lone "unsure" cold line; a real, if rarely-taken, path.
  defp evaluate(:quote_foreign_vdata),
    do: Quote.reify({:vdata, :Ghost, [{:vtype, 0}]}, 0, base_env())

  # Strict-positivity check where the family occurs THROUGH another datatype's
  # constructor field (`Bad`'s ctor takes `Wrap -> Nat`; `Wrap`'s ctor takes
  # `Bad`): `occurs_deep?` must recurse into `Wrap`'s ctors and reject `Bad`.
  defp evaluate(:positivity_through_ctor) do
    env =
      base_env()
      |> Inductive.declare(
        Inductive.family(:Wrap, [], [], 0),
        [Inductive.ctor(:wrapB, [{:a, {:data, :Bad, [], []}}], [], [:unrestricted], [])]
      )
      |> Inductive.declare(
        Inductive.family(:Bad, [], [], 0),
        [
          Inductive.ctor(
            :mkA,
            [{:f, {:pi, Cure.Core.Grade.unrestricted(), {:data, :Wrap, [], []}, @nat}}],
            [],
            [:unrestricted],
            []
          )
        ]
      )

    Inductive.positive?(env, Inductive.family(:Bad, [], [], 0))
  end

  # Deserialize a term carrying a symbol name that is NOT an already-interned
  # atom (adversarial / foreign serialized input): `sym_atom` must fail cleanly
  # with `:unknown_symbol` rather than mint a new permanent atom.
  defp evaluate(:decode_unknown_symbol) do
    enc = Serialize.encode({:global, :Zqxjw})
    Serialize.decode(String.replace(enc, "Zqxjw", "Zzz_never_interned_9973"))
  end

  # Size-change certification of a self-call that UNDER-APPLIES itself
  # (`f(a,b) = f(a)`): the change-matrix row for the missing argument is `nil`,
  # so `arg_relation(nil, _)` yields `:unknown` and the def is (soundly) rejected.
  defp evaluate(:cert_under_application) do
    body =
      {:lam, Cure.Core.Grade.unrestricted(), @nat,
       {:lam, Cure.Core.Grade.unrestricted(), @nat, {:app, {:global, :f}, {:var, 1}}}}

    env =
      Env.add_def(
        base_env(),
        :f,
        {:pi, Cure.Core.Grade.unrestricted(), @nat, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}},
        body
      )

    Cure.Elab.TotalityClosure.provably_total?(env, :f)
  end

  # Certification whose forward reach pulls in a DANGLING callee (`f → g → h`,
  # `h` undefined): `callees_env`/`reaches?` must treat the body-less global as a
  # leaf (`_ -> []`) instead of crashing; with no cycle back to `f` it certifies.
  defp evaluate(:cert_dangling_callee) do
    body_f = {:lam, Cure.Core.Grade.unrestricted(), @nat, {:app, {:global, :g}, {:var, 0}}}
    body_g = {:lam, Cure.Core.Grade.unrestricted(), @nat, {:app, {:global, :h}, {:var, 0}}}

    env =
      base_env()
      |> Env.add_def(:f, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body_f)
      |> Env.add_def(:g, {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat}, body_g)

    Cure.Elab.TotalityClosure.provably_total?(env, :f)
  end

  # -- adversarial "backstop" probes: malformed input at a real kernel boundary --
  # Each feeds the kernel an ill-formed value the upstream checks would normally
  # reject, and asserts the *defensive* clause fires — proving the guard does its
  # job under attack rather than assuming it. The three ι-guards RAISE (a coverage
  # violation / ill-typed value reached the evaluator), so `evaluate` catches the
  # raise and returns `{:raised, message}` for the oracle to inspect.

  # A `case` whose data scrutinee's constructor is absent from the branch set
  # (coverage would reject this upstream): `Eval.eval`'s ι-rule hits `nil` → raise.
  defp evaluate(:eval_no_branch),
    do:
      catch_raise(fn ->
        Eval.eval({:case, {:ctor, :S, [@z]}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, @z}]}, [])
      end)

  # A `case` whose scrutinee evaluates to a non-data value (`{:vint, 3}`): the
  # ι-rule's `other ->` arm raises (an ill-typed case reached eval).
  defp evaluate(:eval_nondata_scrutinee),
    do:
      catch_raise(fn ->
        Eval.eval({:case, {:int_lit, 3}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, [{:Z, 0, @z}]}, [])
      end)

  # β-reducing an argument into a non-function value (over-applied ctor / term
  # that should have been rejected): `Eval.apply`'s catch-all raises.
  defp evaluate(:apply_nonfun),
    do: catch_raise(fn -> Eval.apply({:vint, 3}, {:vint, 4}) end)

  # Convertibility of two constructor values whose ctor is UNKNOWN to a non-nil
  # signature: `coerce_fields`'s `field_count == nil` arm falls back to a strict
  # length compare (sound) instead of crashing. Identical spines ⇒ still convertible.
  defp evaluate(:conv_unknown_ctor_fallback),
    do: Conv.conv?({:ctor, :Foo, [@z]}, {:ctor, :Foo, [@z]}, base_env(), 0, base_env())

  # A def whose BODY is a hole, with `no_hole: :reject` in effect: `check` admits
  # the hole (K3) so it reaches the Final-Core validator, which rejects it —
  # driving `run_final_core_validator`'s `{{:ok,_},{:error,_}}` arm. Restores the
  # app-env config afterwards so the reject override never leaks to other probes.
  defp evaluate(:validator_rejects_hole_body) do
    prev = Application.get_env(:cure, :final_core_config)

    try do
      Application.put_env(:cure, :final_core_config, Map.put(Validator.wave0_config(), :no_hole, :reject))
      env = Env.add_def(base_env(), :holey_body, @nat, {:hole, :h})
      Kernel.check_def(env, :holey_body)
    after
      if prev,
        do: Application.put_env(:cure, :final_core_config, prev),
        else: Application.delete_env(:cure, :final_core_config)
    end
  end

  # -- value-surface probes: the atom / bounded / binary-type / bitwise family the --
  # dependent value surface added, driven through the real kernel entry points
  # (eval / conv / quote / serialize / infer / check / branch_unify / positivity).
  # No term-shaped generator produces these value forms, so they are cold under the
  # live campaign; each probe is a genuine definitional-equality / typing assertion.

  # eval of the three closed value literals: `Atom` type, an atom literal, a compact
  # `Bounded` literal — each reduces to its canonical value with no environment.
  defp evaluate(:eval_value_literals),
    do: {Eval.eval({:atom_type}, []), Eval.eval({:atom_lit, :ok}, []), Eval.eval({:bounded_lit, 3}, [])}

  # ι-reduction over a compact `Bounded` scrutinee: it peels ONE layer to
  # `First` / `Next(pred)` and reuses the ordinary ι-rule. `First` selects the
  # `First` branch; `Next 2` selects `Next`, binding the compact predecessor.
  defp evaluate(:eval_bounded_iota) do
    motive = {:lam, Cure.Core.Grade.unrestricted(), @bounded_ty, @nat}
    branches = [{:First, 1, @z}, {:Next, 2, {:var, 0}}]

    {Eval.eval({:case, {:bounded_lit, 0}, motive, branches}, []),
     Eval.eval({:case, {:bounded_lit, 2}, motive, branches}, [])}
  end

  # The compact-`Bounded` → `First`/`Next` peel used by the ι-rule and cross-rep
  # conversion: `0` ⇒ `First`, `k>0` ⇒ `Next(pred)`; `bounded_to_ctor_if` peels a
  # `{:vbounded, _}` and leaves any other value untouched.
  defp evaluate(:eval_bounded_peel),
    do:
      {Eval.bounded_to_ctor({:vbounded, 0}), Eval.bounded_to_ctor({:vbounded, 3}),
       Eval.bounded_to_ctor_if({:vbounded, 2}), Eval.bounded_to_ctor_if({:vint, 9})}

  # Int bitwise δ-ops fold on two `{:vint, _}` operands (bnot on one): the value-level
  # analogue of the arithmetic ops, exercised across the whole family in one probe.
  defp evaluate(:eval_bitwise_fold),
    do:
      {Eval.fold(:band, [{:vint, 12}, {:vint, 10}]), Eval.fold(:bor, [{:vint, 12}, {:vint, 10}]),
       Eval.fold(:bxor, [{:vint, 12}, {:vint, 10}]), Eval.fold(:bsl, [{:vint, 1}, {:vint, 4}]),
       Eval.fold(:bsr, [{:vint, 32}, {:vint, 2}]), Eval.fold(:bnot, [{:vint, 5}])}

  # A negative de Bruijn index reaching eval (a malformed term the checker rejects
  # upstream): the `{:var, k}` clause guards `k >= 0`, so a negative index falls to the
  # defensive raise rather than silently resolving `Enum.at/2`'s from-the-end index.
  defp evaluate(:eval_negative_debruijn),
    do: catch_raise(fn -> Eval.eval({:var, -1}, []) end)

  # A `case` over a compact `Bounded` scrutinee whose PEELED constructor (`First`) is
  # absent from the branch set: the bounded ι-arm's nil-guard raises the same legible
  # "ι: no branch" coverage-violation as the `vctor` arm (an ill-typed case reached eval).
  defp evaluate(:eval_bounded_no_branch),
    do:
      catch_raise(fn ->
        Eval.eval(
          {:case, {:bounded_lit, 0}, {:lam, Cure.Core.Grade.unrestricted(), @bounded_ty, @nat},
           [{:Next, 2, {:var, 0}}]},
          []
        )
      end)

  # reify each new value form back to its term: compact `Bounded`, `Binary`/`Atom`
  # type formers, and an atom literal — the read-back half of the value surface.
  defp evaluate(:quote_value_surface),
    do:
      {Quote.reify({:vbounded, 4}, 0, base_env()), Quote.reify({:vbinary_type}, 0, base_env()),
       Quote.reify({:vatom_type}, 0, base_env()), Quote.reify({:vatom, :ok}, 0, base_env())}

  # Definitional equality of the atom / atom-type / binary-type value forms:
  # atoms compare by identity, the type formers are reflexively equal.
  defp evaluate(:conv_atom_binary),
    do:
      {Conv.conv_values?({:vatom, :a}, {:vatom, :a}, 0, base_env()),
       Conv.conv_values?({:vatom, :a}, {:vatom, :b}, 0, base_env()),
       Conv.conv_values?({:vatom_type}, {:vatom_type}, 0, base_env()),
       Conv.conv_values?({:vbinary_type}, {:vbinary_type}, 0, base_env())}

  # Cross-representation definitional equality of a compact `Bounded` literal and its
  # `First`/`Next` tower, both directions (`First`≙`0`, `Next`≙`succ`), peeling one
  # compact layer per step — the `Bounded` analogue of the `vnat`↔`S`/`Z` rules.
  defp evaluate(:conv_bounded_crossrep) do
    e = base_env()

    {Conv.conv_values?({:vbounded, 2}, {:vbounded, 2}, 0, e),
     Conv.conv_values?({:vbounded, 0}, {:vctor, :First, [{:vnat, 0}]}, 0, e),
     Conv.conv_values?({:vctor, :First, [{:vnat, 0}]}, {:vbounded, 0}, 0, e),
     Conv.conv_values?({:vbounded, 1}, {:vctor, :Next, [{:vnat, 1}, {:vbounded, 0}]}, 0, e),
     Conv.conv_values?({:vctor, :Next, [{:vnat, 1}, {:vbounded, 0}]}, {:vbounded, 1}, 0, e)}
  end

  # The no-delta fast-path (`same_value_no_delta?`) reached via the arguments of two
  # stuck neutral applications: identical value-surface args short-circuit as equal
  # without any δ-unfolding.
  defp evaluate(:conv_no_delta_value_surface) do
    napp = fn arg -> {:vneutral, {:napp, {:nvar, 0}, arg}} end
    e = base_env()

    {Conv.conv_values?(napp.({:vatom, :a}), napp.({:vatom, :a}), 1, e),
     Conv.conv_values?(napp.({:vatom_type}), napp.({:vatom_type}), 1, e),
     Conv.conv_values?(napp.({:vbinary_type}), napp.({:vbinary_type}), 1, e),
     Conv.conv_values?(napp.({:vbounded, 2}), napp.({:vbounded, 2}), 1, e)}
  end

  # s-expression round-trip of the three new closed term forms: `binary-type`,
  # `atom-type`, and an atom literal must decode back to the identical term.
  defp evaluate(:serialize_value_surface),
    do: for(t <- [{:binary_type}, {:atom_type}, {:atom_lit, :ok}], do: roundtrip(t))

  # Atom literals whose printed form is NOT a bareword — a space-bearing atom (quoted
  # → decoded via the `{:str, _}` `sym_atom` arm) and the empty atom (`bareword?("")`
  # is false) — must still round-trip to the identical atom.
  defp evaluate(:serialize_special_atoms),
    do: {roundtrip({:atom_lit, :"has space"}), roundtrip({:atom_lit, :""})}

  # Decode of a malformed `(atom …)` whose payload is an integer token, not a symbol:
  # `sym_atom` must reject it cleanly with `:malformed_symbol` (a defensive backstop
  # against foreign serialized input) rather than crash.
  defp evaluate(:serialize_malformed_symbol), do: Serialize.decode("(atom 5)")

  # infer of the closed type formers: `Binary` / `Atom` inhabit `Type0`; an atom
  # literal has type `Atom`; a hole in inference position is rejected (K3 admits
  # holes only in checking position).
  defp evaluate(:infer_value_type_formers),
    do:
      {Kernel.infer(ctx(), {:binary_type}), Kernel.infer(ctx(), {:atom_type}), Kernel.infer(ctx(), {:atom_lit, :foo}),
       Kernel.infer(ctx(), {:hole, :h})}

  # infer of a `{:bounded_lit, _}` when the `Bounded` builtin is NOT registered:
  # the guard fires with `:bounded_family_unregistered` rather than minting a witness.
  defp evaluate(:infer_bounded_unregistered), do: Kernel.infer(ctx(), {:bounded_lit, 5})

  # infer of a `{:bounded_lit, k}` against a registered `Bounded`: the minimal witness
  # is `Bounded(k+1)` (the literal `k` inhabits every bound strictly greater than it).
  defp evaluate(:infer_bounded_registered), do: Kernel.infer(bounded_ctx(), {:bounded_lit, 5})

  # check `{:bounded_lit, k}` against `Bounded(bound)` with a concrete in-range bound.
  defp evaluate(:check_bounded_in_range),
    do: Kernel.check(bounded_ctx(), {:bounded_lit, 2}, {:vdata, :Bounded, [{:vnat, 5}]})

  # …against a concrete bound the literal is NOT below: out-of-range rejection.
  defp evaluate(:check_bounded_out_of_range),
    do: Kernel.check(bounded_ctx(), {:bounded_lit, 5}, {:vdata, :Bounded, [{:vnat, 3}]})

  # …against a bound written as an `S`/`Z` tower rather than a compact `vnat`:
  # `concrete_nat` peels the tower to decide the range.
  defp evaluate(:check_bounded_tower),
    do: Kernel.check(bounded_ctx(), {:bounded_lit, 0}, {:vdata, :Bounded, [{:vctor, :S, [{:vctor, :Z, []}]}]})

  # …against a NON-concrete bound: a bare neutral, and a neutral under one `S` layer.
  # Both are rejected as `:bounded_bound_not_concrete` (the bound must reduce to a
  # literal to decide membership). A depth-1 context makes the neutral reifiable.
  defp evaluate(:check_bounded_not_concrete) do
    c = Context.extend(bounded_ctx(), {:vdata, :Nat, []})

    {Kernel.check(c, {:bounded_lit, 2}, {:vdata, :Bounded, [{:vneutral, {:nvar, 0}}]}),
     Kernel.check(c, {:bounded_lit, 2}, {:vdata, :Bounded, [{:vctor, :S, [{:vneutral, {:nvar, 0}}]}]})}
  end

  # check `{:bounded_lit, _}` against a type that is NOT the bounded family (`Int`):
  # the family mismatch surfaces as a conversion failure.
  defp evaluate(:check_bounded_wrong_family),
    do: Kernel.check(bounded_ctx(), {:bounded_lit, 2}, {:vint_type})

  # check a ctor whose inferred family does not match a non-`vdata` goal (`Int`):
  # the ctor `check` clause falls through to `check_via_infer`, which rejects.
  defp evaluate(:check_ctor_via_infer),
    do: Kernel.check(ctx(), {:ctor, :Z, []}, {:vint_type})

  # motive-sort of a `case` whose motive returns `Binary` / `Atom`: the well-formedness
  # check must sort those type-former VALUES to `Type0` (`infer_type_value_sort`).
  defp evaluate(:sort_value_type_formers) do
    c = Context.extend(ctx(), {:vdata, :Bool, []})
    branches = [{:False, 0, {:hole, :h}}, {:True, 0, {:hole, :h}}]

    {Kernel.infer(
       c,
       {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bool, [], []}, {:binary_type}}, branches}
     ),
     Kernel.infer(
       c,
       {:case, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bool, [], []}, {:atom_type}}, branches}
     )}
  end

  # The index-unifier's compact-`Bounded`↔`First`/`Next` bridge: equal literals and
  # matching towers unify (`:trivial`); every cross-constructor / off-by-one pairing
  # is rejected (`:impossible`) — both directions, driven through `branch_unify/5`.
  defp evaluate(:unify_bounded_bridge) do
    {unify_index([{:bounded_lit, 2}], [{:vbounded, 2}]), unify_index([{:bounded_lit, 2}], [{:vbounded, 3}]),
     unify_index([{:bounded_lit, 0}], [{:vctor, :First, [{:vnat, 0}]}]),
     unify_index([{:ctor, :First, [{:nat_lit, 0}]}], [{:vbounded, 0}]),
     unify_index([{:bounded_lit, 1}], [{:vctor, :Next, [{:vnat, 1}, {:vbounded, 0}]}]),
     unify_index([{:ctor, :Next, [{:nat_lit, 1}, {:bounded_lit, 0}]}], [{:vbounded, 1}]),
     unify_index([{:bounded_lit, 0}], [{:vctor, :Next, [{:vnat, 1}, {:vbounded, 0}]}]),
     unify_index([{:ctor, :Next, [{:nat_lit, 1}, {:bounded_lit, 0}]}], [{:vbounded, 0}]),
     unify_index([{:bounded_lit, 2}], [{:vctor, :First, [{:vnat, 0}]}]),
     unify_index([{:ctor, :First, [{:nat_lit, 0}]}], [{:vbounded, 2}])}
  end

  # A rigid value-surface head (`Binary`/`Atom` type formers, an atom literal, a
  # compact `Bounded` literal) clashing with an unrelated rigid index (`Int`): each
  # is `rigid_index?`, so the mismatch is a definite `:impossible`.
  defp evaluate(:unify_rigid_value_heads),
    do:
      {unify_index([{:binary_type}], [{:vint, 7}]), unify_index([{:atom_type}], [{:vint, 7}]),
       unify_index([{:atom_lit, :x}], [{:vint, 7}]), unify_index([{:bounded_lit, 2}], [{:vint, 7}])}

  # `opaque type` (a postulate): `opaque_family/3` builds the marker family and
  # `opaque?/2` reports it as opaque once declared.
  defp evaluate(:opaque_family_positivity) do
    ofam = Inductive.opaque_family(:Eff, [], 0)
    env = Inductive.declare(base_env(), ofam, [])
    {ofam, Inductive.opaque?(env, :Eff)}
  end

  # Strict-positivity through a global type-synonym: (a) an alias in a ctor FIELD that
  # expands to the family itself is rejected; (b) an alias in a ctor-field arrow DOMAIN
  # (negative, benign) is accepted; (c) a dangling/opaque global in a domain is treated
  # as a leaf and accepted. Exercises the alias-expanding `gather_data_heads` walk.
  defp evaluate(:positivity_alias_expansion) do
    ea =
      base_env()
      |> Env.add_def(:Syn2, {:type, 0}, {:data, :HS, [], []})
      |> Inductive.declare(Inductive.family(:HS, [], [], 0), [
        Inductive.ctor(:mkS, [{:f, {:global, :Syn2}}], [], [:unrestricted], [])
      ])

    eb =
      base_env()
      |> Env.add_def(:Syn, {:type, 0}, {:data, :Foo, [], []})
      |> Inductive.declare(Inductive.family(:Foo, [], [], 0), [])
      |> Inductive.declare(Inductive.family(:Host, [], [], 0), [
        Inductive.ctor(
          :mkH,
          [{:f, {:pi, Cure.Core.Grade.unrestricted(), {:global, :Syn}, @nat}}],
          [],
          [:unrestricted],
          []
        )
      ])

    ec =
      Inductive.declare(base_env(), Inductive.family(:HU, [], [], 0), [
        Inductive.ctor(
          :mkU,
          [{:f, {:pi, Cure.Core.Grade.unrestricted(), {:global, :Unknown}, @nat}}],
          [],
          [:unrestricted],
          []
        )
      ])

    {Inductive.positive?(ea, Inductive.family(:HS, [], [], 0)),
     Inductive.positive?(eb, Inductive.family(:Host, [], [], 0)),
     Inductive.positive?(ec, Inductive.family(:HU, [], [], 0))}
  end

  # A family that refers to itself as a bare `{:global, name}` (rather than the usual
  # `{:data, name, …}` spelling): the name-collision guard in `occurs?` still detects
  # the self-reference and rejects the non-strictly-positive occurrence.
  defp evaluate(:occurs_bare_global) do
    env =
      Inductive.declare(base_env(), Inductive.family(:HN, [], [], 0), [
        Inductive.ctor(:mkN, [{:f, {:global, :HN}}], [], [:unrestricted], [])
      ])

    Inductive.positive?(env, Inductive.family(:HN, [], [], 0))
  end

  # The `whnf/2` arity clause (default opts) — reached only by a direct call, never by
  # the kernel's own `whnf/3` / `whnf_value` internal callers.
  defp evaluate(:whnf_arity2_direct), do: Normalise.whnf(ctx(), {:nat_lit, 3})

  # Nested fuel scopes: an inner `with_fuel` running inside an outer one must RESTORE
  # the outer bound on exit (not delete the key), so the outer computation keeps its
  # bound. Both a nested and the subsequent outer reduction complete normally.
  defp evaluate(:whnf_nested_fuel_restore) do
    Normalise.with_fuel(8, fn ->
      inner =
        Normalise.with_fuel(4, fn ->
          Normalise.whnf(ctx(), {:app, {:lam, Cure.Core.Grade.unrestricted(), @nat, {:var, 0}}, {:nat_lit, 3}})
        end)

      {inner, Normalise.whnf(ctx(), {:nat_lit, 5})}
    end)
  end

  # -- certificate backstops: a malformed Core body fed to `terminating?/3` must be --
  # walked by the fail-closed fallbacks (unknown node shapes / non-tuple term slots)
  # and soundly rejected (`false`), never crash the size-change analysis.

  # An unknown tuple node (`{:foo, child}`) whose child self-calls `:f`: the tuple
  # fallback recurses via `walk`.
  defp evaluate(:cert_unknown_tuple_node),
    do: cert_terminates?({:lam, Cure.Core.Grade.unrestricted(), @nat, {:foo, {:app, {:global, :f}, {:var, 0}}}})

  # An unknown node carrying a LIST child (`{:blk, [call]}`): the fallback descends
  # each list element.
  defp evaluate(:cert_unknown_list_node),
    do: cert_terminates?({:lam, Cure.Core.Grade.unrestricted(), @nat, {:blk, [{:app, {:global, :f}, {:var, 0}}]}})

  # A non-tuple term in a call-argument slot (`f(7)`): `walk` on the bare int `7` hits
  # the non-tuple catch-all.
  defp evaluate(:cert_nontuple_call_arg),
    do: cert_terminates?({:lam, Cure.Core.Grade.unrestricted(), @nat, {:app, {:global, :f}, 7}})

  # A non-tuple element inside an unknown node's list child (`{:blk, [99, call]}`):
  # `descend_unknown` skips the bare int `99`.
  defp evaluate(:cert_nontuple_list_elem),
    do: cert_terminates?({:lam, Cure.Core.Grade.unrestricted(), @nat, {:blk, [99, {:app, {:global, :f}, {:var, 0}}]}})

  # A non-tuple term to the LEFT of an application (`(7)(f)`): the `calls?` fast-path
  # hits its non-tuple catch-all before the right operand's self-call short-circuits.
  defp evaluate(:cert_calls_nontuple_head),
    do: cert_terminates?({:lam, Cure.Core.Grade.unrestricted(), @nat, {:app, 7, {:global, :f}}})

  # -- editions-facility probes: the edition-derived keyword set and the migrate --
  # fixpoint loop (Editions initiative), driven through their real public entry
  # points (`Cure.Edition.retired_keywords/2`, `Cure.Migrate.run_to_fixpoint/2`).
  # No term-shaped generator reaches this non-kernel migration surface.

  # `retired_keywords/2` over a fixture rule set: a rule enforced AT the queried
  # edition retires its keyword (`compare == :eq`), one enforced at a FUTURE edition
  # does not yet (`:lt`), and an `enforced_in: nil` rule never does. Only "proto"
  # qualifies at "2027".
  defp evaluate(:edition_retired_keywords) do
    rules = [
      fixture_rule(:W_fx_proto, "2027", ["proto"]),
      fixture_rule(:W_fx_future, "2099", ["impl"]),
      fixture_rule(:W_fx_never, nil, ["receive"])
    ]

    Cure.Edition.retired_keywords("2027", rules)
  end

  # `run_to_fixpoint/2` on a two-rule chain whose second rule (append `:b`) is
  # exposed only after the first (append `:a`) fires: convergence requires a
  # re-scan pass, then a no-rewrite pass — driving `do_fixpoint`'s changing-pass →
  # verify → recurse arm and its fixpoint-reached arm. Reports whether both marks
  # landed.
  defp evaluate(:migrate_fixpoint_converges) do
    rules = [append_marker_rule(:b, "a", "b"), append_marker_rule(:a, nil, "a")]

    case Cure.Migrate.run_to_fixpoint(fixpoint_ast(), rules: rules) do
      {:ok, {:block, _m, ex}, _warns} ->
        {Enum.any?(ex, &match?({:literal, _, "a"}, &1)), Enum.any?(ex, &match?({:literal, _, "b"}, &1))}

      other ->
        other
    end
  end

  # A minimal migration `Rule` fixture carrying only the fields `retired_keywords/2`
  # reads (`enforced_in` + `retires_keywords`); its rewrite is inert.
  defp fixture_rule(id, enforced_in, retires) do
    %Rule{
      id: id,
      description: "fixture",
      phase: :syntactic,
      tier: :review,
      since: "2026",
      warning_template: "m",
      enforced_in: enforced_in,
      retires_keywords: retires,
      detect_and_rewrite: fn _ast, _ctx -> :no_change end
    }
  end

  # A `:machine`-tier fixture rule that appends the string literal `mark` to the
  # top-level block once `needle` is present (`needle == nil` ⇒ unconditional),
  # and only once — so the rule set reaches a genuine fixpoint.
  defp append_marker_rule(id, needle, mark) do
    %Rule{
      id: id,
      description: "fixture",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      warning_template: "m",
      detect_and_rewrite: fn {:block, m, ex}, _ctx ->
        has = needle == nil or Enum.any?(ex, &match?({:literal, _, ^needle}, &1))
        already = Enum.any?(ex, &match?({:literal, _, ^mark}, &1))

        if has and not already,
          do: {:rewrite, {:block, m, ex ++ [{:literal, [subtype: :string], mark}]}},
          else: :no_change
      end
    }
  end

  # A real, printable + reparseable whole-file AST (with trivia attached) for the
  # fixpoint probe — the verify step reprints and reparses each changing pass.
  defp fixpoint_ast do
    {:ok, toks, trivia} = Lexer.tokenize("mod M\nfn f(x: Int) -> Int = 1\n", trivia: true)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Trivia.attach(ast, trivia)
  end

  # round-trip a term through the s-expression serializer.
  defp roundtrip(term), do: {term, Serialize.decode(IO.iodata_to_binary(Serialize.encode(term)))}

  defp catch_raise(fun) do
    {:returned, fun.()}
  rescue
    e -> {:raised, Exception.message(e)}
  end

  defp ctx, do: Context.empty(base_env())

  # -- oracle: the verdict each probe MUST return --
  defp matches?(:infer_absurd, r), do: r == {:error, :absurd_in_reachable_position}
  defp matches?(:infer_fields_only_ctor, r), do: match?({:error, {:ctor_requires_checking_mode, _}}, r)
  defp matches?(:check_ctor_arity, r), do: r == {:error, :ctor_arity}
  defp matches?(:check_def_unknown, r), do: Cure.Diagnostic.key(r) == :unknown_global
  defp matches?(:check_def_builtin_op, r), do: r == :ok
  defp matches?(:validate_cert_builtin_op, r), do: match?({:ok, _}, r)
  defp matches?(:family_ceiling, r), do: r == {:error, :universe_ceiling}
  defp matches?(:normalize_opts, r), do: r == {:nat_lit, 3}
  defp matches?(:validator_warn_emit, r), do: r == :ok
  # The field error must survive unremapped (NOT rewritten to :index_mismatch).
  defp matches?(:remap_index_passthrough, r), do: match?({:error, {:conversion_failure, _, _}}, r)
  defp matches?(:quote_foreign_vdata, r), do: match?({:data, :Ghost, _, _}, r)
  defp matches?(:positivity_through_ctor, r), do: r == {:error, {:non_strictly_positive, :mkA}}
  defp matches?(:decode_unknown_symbol, r), do: match?({:error, {:unknown_symbol, _}}, r)
  # Under-application cannot be certified decreasing → soundly rejected (false).
  defp matches?(:cert_under_application, r), do: r == false
  # No cycle back to `f` through the dangling callee → certified total (true).
  defp matches?(:cert_dangling_callee, r), do: r == true

  # -- backstop oracles: the guard MUST fire (raise the documented ι-error / reject) --
  defp matches?(:eval_no_branch, r), do: match?({:raised, "ι: no branch" <> _}, r)
  defp matches?(:eval_nondata_scrutinee, r), do: match?({:raised, "ι: non-data scrutinee" <> _}, r)
  defp matches?(:apply_nonfun, r), do: match?({:raised, "Eval.apply:" <> _}, r)
  defp matches?(:conv_unknown_ctor_fallback, r), do: r == true
  defp matches?(:validator_rejects_hole_body, r), do: match?({:error, {:final_core_violation, _}}, r)

  # -- value-surface oracles (definitional-equality / typing verdicts) --
  defp matches?(:eval_value_literals, r), do: r == {{:vatom_type}, {:vatom, :ok}, {:vbounded, 3}}
  defp matches?(:eval_negative_debruijn, r), do: match?({:raised, "eval: negative de Bruijn" <> _}, r)
  defp matches?(:eval_bounded_no_branch, r), do: match?({:raised, "ι: no branch" <> _}, r)
  defp matches?(:eval_bounded_iota, r), do: r == {{:vctor, :Z, []}, {:vbounded, 1}}

  defp matches?(:eval_bounded_peel, r),
    do:
      r ==
        {{:vctor, :First, [{:vnat, 0}]}, {:vctor, :Next, [{:vnat, 3}, {:vbounded, 2}]},
         {:vctor, :Next, [{:vnat, 2}, {:vbounded, 1}]}, {:vint, 9}}

  defp matches?(:eval_bitwise_fold, r),
    do:
      r ==
        {{:ok, {:vint, 8}}, {:ok, {:vint, 14}}, {:ok, {:vint, 6}}, {:ok, {:vint, 16}}, {:ok, {:vint, 8}},
         {:ok, {:vint, -6}}}

  defp matches?(:quote_value_surface, r),
    do: r == {{:bounded_lit, 4}, {:binary_type}, {:atom_type}, {:atom_lit, :ok}}

  defp matches?(:conv_atom_binary, r), do: r == {true, false, true, true}
  defp matches?(:conv_bounded_crossrep, r), do: r == {true, true, true, true, true}
  defp matches?(:conv_no_delta_value_surface, r), do: r == {true, true, true, true}

  defp matches?(:serialize_value_surface, r),
    do:
      r == [
        {{:binary_type}, {:ok, {:binary_type}}},
        {{:atom_type}, {:ok, {:atom_type}}},
        {{:atom_lit, :ok}, {:ok, {:atom_lit, :ok}}}
      ]

  defp matches?(:serialize_special_atoms, r),
    do:
      r == {{{:atom_lit, :"has space"}, {:ok, {:atom_lit, :"has space"}}}, {{:atom_lit, :""}, {:ok, {:atom_lit, :""}}}}

  defp matches?(:serialize_malformed_symbol, r), do: r == {:error, :malformed_symbol}

  defp matches?(:infer_value_type_formers, r),
    do: r == {{:ok, {:vtype, 0}}, {:ok, {:vtype, 0}}, {:ok, {:vatom_type}}, {:error, {:hole_in_inference_position, :h}}}

  defp matches?(:infer_bounded_unregistered, r), do: r == {:error, :bounded_family_unregistered}
  defp matches?(:infer_bounded_registered, r), do: r == {:ok, {:vdata, :Bounded, [{:vnat, 6}]}}
  defp matches?(:check_bounded_in_range, r), do: r == :ok
  defp matches?(:check_bounded_out_of_range, r), do: r == {:error, {:bounded_lit_out_of_range, 5, 3}}
  defp matches?(:check_bounded_tower, r), do: r == :ok

  defp matches?(:check_bounded_not_concrete, r),
    do:
      r ==
        {{:error, {:bounded_bound_not_concrete, {:var, 0}}},
         {:error, {:bounded_bound_not_concrete, {:ctor, :S, [{:var, 0}]}}}}

  defp matches?(:check_bounded_wrong_family, r), do: match?({:error, {:conversion_failure, {:bounded_lit, 2}, _}}, r)
  defp matches?(:check_ctor_via_infer, r), do: match?({:error, {:conversion_failure, _, _}}, r)
  defp matches?(:sort_value_type_formers, r), do: r == {{:ok, {:vbinary_type}}, {:ok, {:vatom_type}}}

  # equal literals / matching towers unify (`:trivial`); every clash is `:impossible`.
  defp matches?(:unify_bounded_bridge, r),
    do:
      r ==
        {:trivial, :impossible, :trivial, :trivial, :trivial, :trivial, :impossible, :impossible, :impossible,
         :impossible}

  defp matches?(:unify_rigid_value_heads, r), do: r == {:impossible, :impossible, :impossible, :impossible}
  defp matches?(:opaque_family_positivity, r), do: match?({%{opaque: true}, true}, r)
  defp matches?(:positivity_alias_expansion, r), do: r == {{:error, {:non_strictly_positive, :mkS}}, :ok, :ok}
  defp matches?(:occurs_bare_global, r), do: r == {:error, {:non_strictly_positive, :mkN}}
  defp matches?(:whnf_arity2_direct, r), do: r == {:nat_lit, 3}
  defp matches?(:whnf_nested_fuel_restore, r), do: r == {{:nat_lit, 3}, {:nat_lit, 5}}

  # -- editions-facility oracles --
  # Only the rule enforced at (≤) "2027" retires its keyword; future/nil rules do not.
  defp matches?(:edition_retired_keywords, r), do: r == ["proto"]
  # The chained rule set converges with both marks appended (no divergence / verify abort).
  defp matches?(:migrate_fixpoint_converges, r), do: r == {true, true}

  # every malformed body is soundly rejected (not certified terminating), never a crash.
  defp matches?(cert, r)
       when cert in [
              :cert_unknown_tuple_node,
              :cert_unknown_list_node,
              :cert_nontuple_call_arg,
              :cert_nontuple_list_elem,
              :cert_calls_nontuple_head
            ],
       do: r == false
end
