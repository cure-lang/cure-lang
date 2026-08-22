defmodule Cure.Elab.ErasureRelevanceTest do
  @moduledoc """
  The `{0,ω}` relevance CHECK (M8.3) — the piece that makes erasure *sound*.

  Cure already MARKS binders (implicit `{n: Nat}` fn params and GADT index args
  get quantity `:erased`; `declarations.ex:173`, `erasure_marking_test.exs`) and
  already ERASES them (`erase.ex` drops erased ctor args + erased global-app-spine
  args). What is MISSING is the check that an *erased* binder is never used in a
  runtime-RELEVANT position — without it, `fn f({n: Nat}, v: NV(n)) -> Nat = n`
  type-checks, then erasure drops the `n` slot the body still returns, so the
  emitted BEAM function references a dropped binding. This file characterizes
  that hole (red), pinning the exact error shape A2's `Relevance.check` must emit.

  ## Idris 0/ω grounding (Core/LinearCheck.idr, ω-except-erased slice ONLY)

  Re-read from source (`~/Develop/esp32-beam/reference/idris2/src/Core/LinearCheck.idr`)
  at the top of this task. `lcheck rig erase env term` threads a usage count; a
  binder declared `Rig0` (our `:erased`) must have usage 0 in every RELEVANT
  position. The multiplier is `checkRig = rigf |*| rig` (App case, :288), and
  `erased |*| _ = erased`, so:

    * RELEVANT for a `0` binder (usage counts → violation):
      - RETURNED as the value (the term IS the binder);
      - passed in a `ω` / `:unrestricted` argument position (`rigf` present → `checkRig`
        stays `rig`);
      - SCRUTINISED (case discriminant is checked at the ambient `rig`);
      - APPLIED as a function head.
    * EXEMPT (checked at `erased`, usage does NOT count):
      - type / index positions — Pi & Sigma DOMAINS are checked `erased` when the
        binder is inspectable-only (`rig` local, :265-272); the motive likewise;
      - erased ARGUMENT positions (`rigf` erased → `checkRig` erased, :288);
      - `Eq` / proof positions — `Refl`'s argument is `Rig0`; Cure's
        `reflexive` carries an ERASED witness (nullary at runtime) and the
        J/subst transport's proof scrutinee is dropped wholesale by the
        collapsible-family erasure, so proof-position use is runtime-free.

  We port the 0/ω slice only (per the manifest caveat: read Idris core as
  ω-except-erased; the linear `1` multiplicity is deliberately out of scope).

  RED STATUS (this commit): probes (a)–(c) currently elaborate `{:ok, _}` — the
  hole. Controls (d)–(e) already pass and must STAY green through A2.
  """
  # async: false — the seam tests below load a BEAM module (Emit.compile_and_load),
  # which mutates global VM state, so this module must not run concurrently.
  use ExUnit.Case, async: false
  alias Cure.Elab.{Program, Erase, Emit}
  alias Cure.Core.Env
  alias Cure.Diagnostic.Renderer

  # Nat, the singleton family SNat(n), the indexed family NV(n) (so `v : NV(n)`
  # makes `n` genuinely occur only in a TYPE position in the signature), plus the
  # reflection helpers. Identical shape to value_in_goal_match_test's preamble.
  @preamble """
    type Nat = Z | S(Nat)
    type SNat indices (n: Nat)
      szero : SNat(Z)
      ssuc : SNat(n) -> SNat(S(n))
    type NV indices (n: Nat)
      vz : NV(Z)
      vs : SNat(n) -> NV(S(n))
    fn toS(m: Nat) -> SNat(m) = match m
      Z() -> szero()
      S(j) -> ssuc(toS(j))
  """
  defp mod(b), do: "mod P\n" <> @preamble <> b <> "end\n"

  describe "erased implicit used relevantly — must be rejected (M8.3 hole)" do
    test "(a) body RETURNS the erased implicit `n`" do
      # `n : Nat` is an erased implicit; the body returns it. Erasure will drop
      # the `n` slot, so the emitted function returns a dropped binding.
      src =
        mod("""
          fn f({n: Nat}, v: NV(n)) -> Nat = n
        """)

      assert {:error, error} = Program.elaborate(src, file: "relevance.cure")
      assert {:erased_used_relevantly, _} = Program.semantic_error(error)

      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "relevance.cure", src)

      assert Renderer.plain(diagnostic, registry, width: 80) ==
               String.trim_trailing("""
               -- ERASED VALUE USED RELEVANTLY [E104] -------------------------- relevance.cure

               The erased parameter `n` is used as the function's runtime result, but erased
               parameters do not exist at runtime.

               at relevance.cure:12:37
               12 |   fn f({n: Nat}, v: NV(n)) -> Nat = n
                  |         -                           ^ `n` is erased here; this returns an erased value at runtime

               Hint: Declare `n` as a runtime parameter, or keep it out of runtime expressions
               """)

      assert_relevance_lsp(Renderer.lsp(diagnostic, registry),
        primary: {11, 36, 37},
        binder: {11, 8, 9}
      )
    end

    test "(b) erased implicit `n` passed in a PRESENT argument position" do
      # `g` takes a runtime-relevant `Nat`; passing the erased `n` into it is a
      # relevant use even though `n` is never syntactically returned.
      src =
        mod("""
          fn g(m: Nat) -> Nat = m
          fn f({n: Nat}, v: NV(n)) -> Nat = g(n)
        """)

      assert {:error, error} = Program.elaborate(src, file: "relevance_arg.cure")
      assert {:erased_used_relevantly, _} = Program.semantic_error(error)

      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "relevance_arg.cure", src)

      assert Renderer.plain(diagnostic, registry, width: 80) ==
               String.trim_trailing("""
               -- ERASED VALUE USED RELEVANTLY [E104] ---------------------- relevance_arg.cure

               The erased parameter `n` is used as an argument that exists at runtime, but
               erased parameters do not exist at runtime.

               at relevance_arg.cure:13:39
               13 |   fn f({n: Nat}, v: NV(n)) -> Nat = g(n)
                  |         -                             ^ `n` is erased here; this passes an erased value to a runtime argument

               Hint: Declare `n` as a runtime parameter, or keep it out of runtime expressions
               """)

      assert_relevance_lsp(Renderer.lsp(diagnostic, registry),
        primary: {12, 38, 39},
        binder: {12, 8, 9}
      )
    end

    test "(c) body SCRUTINISES the erased implicit `n`" do
      # Matching on `n` forces its runtime value — a relevant use.
      src =
        mod("""
          fn f({n: Nat}, v: NV(n)) -> Nat =
            match n
              Z() -> Z()
              S(k) -> Z()
        """)

      assert {:error, error} = Program.elaborate(src, file: "relevance_match.cure")
      assert {:erased_used_relevantly, _} = Program.semantic_error(error)

      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "relevance_match.cure", src)

      assert Renderer.plain(diagnostic, registry, width: 80) ==
               String.trim_trailing("""
               -- ERASED VALUE USED RELEVANTLY [E104] -------------------- relevance_match.cure

               The erased parameter `n` is used as the value inspected by a runtime match, but
               erased parameters do not exist at runtime.

               at relevance_match.cure:13:11
               12 |   fn f({n: Nat}, v: NV(n)) -> Nat =
                  |         - `n` is erased here
               13 |     match n
                  |           ^ this match inspects an erased value at runtime

               Hint: Declare `n` as a runtime parameter, or keep it out of runtime expressions
               """)

      assert_relevance_lsp(Renderer.lsp(diagnostic, registry),
        primary: {12, 10, 11},
        binder: {11, 8, 9}
      )
    end
  end

  defp assert_relevance_lsp(lsp, primary: {line, start_char, end_char}, binder: binder) do
    assert lsp["code"] == "E104"

    assert lsp["range"] == %{
             "start" => %{"line" => line, "character" => start_char},
             "end" => %{"line" => line, "character" => end_char}
           }

    assert [%{"message" => "`n` is erased here", "location" => %{"range" => range}}] =
             lsp["relatedInformation"]

    {binder_line, binder_start, binder_end} = binder

    assert range == %{
             "start" => %{"line" => binder_line, "character" => binder_start},
             "end" => %{"line" => binder_line, "character" => binder_end}
           }
  end

  describe "erased implicit used only irrelevantly — must be accepted (controls)" do
    test "(d) erased implicit used only in a TYPE/index position" do
      # `n` appears only inside the types `NV(n)` (param and result); the body
      # returns the runtime-relevant `v`. This is the whole point of erasure and
      # must accept before AND after the check.
      src =
        mod("""
          fn f({n: Nat}, v: NV(n)) -> NV(n) = v
        """)

      assert {:ok, _} = Program.elaborate(src)
    end

    test "(e) erased implicit used only inside an Eq/proof position" do
      # `n` occurs in the return TYPE `Equivalent(Nat, n, n)` (type position) and inside
      # `reflexive(n)` (a proof term; reflexive's witness field is erased, so
      # the runtime value is the nullary reflexive ctor). No relevant use, so
      # it must accept before AND after the check.
      src =
        mod("""
          fn f({n: Nat}, v: NV(n)) -> Equivalent(Nat, n, n) = reflexive(n)
        """)

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  # --- A3: erasure-seam consistency pins ---------------------------------------
  # These pin behaviours that are currently only implementation accidents, so a
  # future refactor cannot silently break the erasure story.

  describe "seam: erased constructor fields are unnameable" do
    @seam_pre """
    mod P
      type Nat = Z | S(Nat)
      type SNat indices (n: Nat)
        szero : SNat(Z)
        ssuc : SNat(n) -> SNat(S(n))
      type NV indices (n: Nat)
        vz : NV(Z)
        vs : SNat(n) -> NV(S(n))
    """

    test "naming the erased index of a matched constructor is an error, not a silent bind" do
      # `vs : SNat(n) -> NV(S(n))` has quantities [:erased (n), :unrestricted (SNat)].
      # In `vs(s)` the surface var `s` names the PRESENT field; the erased index
      # `n` gets the unnameable placeholder `"_erased"` (elaborator `branch_scope`).
      # Referencing `n` in the body must NOT resolve to the erased slot — it is
      # simply unbound.
      src = @seam_pre <> "  fn f(v: NV(S(Z))) -> Nat =\n    match v\n      vs(s) -> n\nend\n"
      assert {:error, _} = Program.elaborate(src)
    end

    test "the present field of the same constructor IS nameable (contrast)" do
      src = @seam_pre <> "  fn f(v: NV(S(Z))) -> NV(S(Z)) =\n    match v\n      vs(s) -> vs(s)\nend\n"
      assert {:ok, _} = Program.elaborate(src)
    end

    test "an explicit erased field after runtime fields receives a synthetic branch slot" do
      src = """
      mod ExplicitErasedBranchSlot
        type Nat = Z | S(Nat)
        type Outcome indices ()
          Resource : (depth: Nat) -> (@erased proof: Nat) -> Outcome

        fn preserve(outcome: Outcome) -> Outcome = match outcome
          Resource(_, _) -> outcome
      end
      """

      assert {:ok, _} = Program.elaborate(src)
    end
  end

  describe "seam: erased params give consistent emitted head/call-site arities" do
    @arity_src """
    type Dec = Dcoupled | Causal
    type Sig = CSig | ESig
    type SVDesc = SVNil | SVCons(Sig, SVDesc)
    fn andd(x: Dec, y: Dec) -> Dec = x
    type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
      prim : SF(as, bs, Causal)
      seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
    fn compose({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, {d1: Dec}, {d2: Dec}, l: SF(as, bs, d1), r: SF(bs, cs, d2)) -> SF(as, cs, andd(d1, d2)) = seq(l, r)
    fn compose3({as: SVDesc}, {bs: SVDesc}, {cs: SVDesc}, {ds: SVDesc}, {d1: Dec}, {d2: Dec}, {d3: Dec}, x: SF(as, bs, d1), y: SF(bs, cs, d2), z: SF(cs, ds, d3)) -> SF(as, ds, andd(andd(d1, d2), d3)) = compose(compose(x, y), z)
    """

    test "erased params drop from the emitted head, and call sites agree end-to-end" do
      {:ok, env} = Program.elaborate(@arity_src)

      arities =
        env
        |> Emit.module_forms(:"Cure.ErasureSeam.Arity", [:compose, :compose3])
        |> Enum.flat_map(fn
          {:function, _, name, arity, _} -> [{name, arity}]
          _ -> []
        end)
        |> Map.new()

      # compose: 5 erased indices + 2 present ⇒ arity 2; compose3: 7 erased + 3 ⇒ 3.
      assert arities[:compose] == 2
      assert arities[:compose3] == 3

      {:ok, mod} =
        Emit.compile_and_load(env,
          module: :"Cure.ErasureSeam.Arity",
          functions: [:compose, :compose3]
        )

      # compose3's body is `compose(compose(x, y), z)`: the emitted call sites pass
      # exactly 2 args to the emitted `compose/2`. A head/call-site arity mismatch
      # would crash `undef` here — a successful nested build IS the arity pin.
      assert apply(mod, :compose3, [:prim, :prim, :prim]) ==
               {:seq, {:seq, :prim, :prim}, :prim}
    end
  end

  describe "seam: proofs are erased (proof irrelevance)" do
    # (The primitive `{:rewrite}`-node version of the proof-irrelevance pin was
    # retired with the form itself — group-A removal commit; its :case-transport
    # twin below was cross-checked side by side first.)
    # (The {:refl}/{:eq}→cure_refl/cure_eq placeholder pins retired with the
    # primitive forms — group-B removal commit; the inductive twins below were
    # cross-checked side by side first: reflexive is nullary at runtime via its
    # erased witness, no placeholder atom needed.)

    # Phase C twins (add-then-retire): the primitive proof forms retire; proof
    # irrelevance must survive on the inductive vehicle. `reflexive`'s witness
    # is an erased field (nullary at runtime), and the J/subst `:case`
    # transport is a collapsible-family elimination whose PROOF vanishes at
    # erase — swapping proofs changes nothing observable.
    test "two different :case-transport proofs erase to the same runtime term" do
      env = Cure.Core.Builtins.seed(Env.empty(), MapSet.new())
      body = {:ctor, :Causal, []}
      motive = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, body}

      id_branch =
        {:reflexive, 1, {:lam, Cure.Core.Grade.unrestricted(), {:app, motive, {:ctor, :Dcoupled, []}}, {:var, 0}}}

      t1 = {:app, {:case, {:ctor, :reflexive, [{:ctor, :Dcoupled, []}]}, motive, [id_branch]}, body}
      t2 = {:app, {:case, {:ctor, :reflexive, [{:ctor, :Causal, []}]}, motive, [id_branch]}, body}

      assert Erase.erase(env, t1) == Erase.erase(env, t2)
      # The collapsible case is GONE from the runtime term (the proof with it);
      # what remains is the identity redex over the erased body.
      assert {:app, {:lam, _g, _dom, {:var, 0}}, erased_body} = Erase.erase(env, t1)
      assert erased_body == Erase.erase(env, body)
    end

    test "a reflexive proof value is runtime-free (erased witness => nullary ctor)" do
      env = Cure.Core.Builtins.seed(Env.empty(), MapSet.new())
      assert Erase.erase(env, {:ctor, :reflexive, [{:ctor, :Dcoupled, []}]}) == {:ctor, :reflexive, []}
    end
  end

  describe "Erase and Relevance agree on what a constructor application is" do
    # The elaborated ctor name may be bare or module-qualified (`:ssuc` vs `:"P.ssuc"`).
    defp ctor_atom(env, base) do
      Enum.find([base, String.to_atom("P." <> to_string(base))], base, fn c ->
        is_list(Cure.Core.Inductive.ctor_quantities(env, c))
      end)
    end

    defp snat_env do
      {:ok, env} = Program.elaborate(mod(""))
      env
    end

    # `ssuc`'s quantities are `[:erased, :unrestricted]` — the auto-generalized index `n` at
    # position 0, the explicit `SNat(n)` field at position 1.

    test "a constructor heading a curried spine erases like the same constructor as a flat node" do
      # `Erase.erase/2`'s `{:app, _, _}` clause special-cased only a `{:global, _}` head; every
      # other head fell through to a fallback that kept ALL arguments with no quantity filter.
      # So the erased index survived into the runtime term, and two Core encodings of one value
      # erased to two different runtime shapes — erasure was not invariant under the eta-shape
      # difference that Idris's LinearCheck and Agda's `@0` are invariant under.
      env = snat_env()
      ssuc = ctor_atom(env, :ssuc)

      erased_index = {:nat_lit, 0}
      present_field = {:ctor, ctor_atom(env, :szero), []}

      flat = Erase.erase(env, {:ctor, ssuc, [erased_index, present_field]})
      spine = Erase.erase(env, {:app, {:app, {:ctor, ssuc, []}, erased_index}, present_field})

      assert flat == {:ctor, ssuc, [present_field]}
      assert spine == flat
    end

    test "erasing an already-erased curried spine is idempotent" do
      env = snat_env()
      ssuc = ctor_atom(env, :ssuc)
      present_field = {:ctor, ctor_atom(env, :szero), []}

      once = Erase.erase(env, {:app, {:app, {:ctor, ssuc, []}, {:nat_lit, 0}}, present_field})
      assert Erase.erase(env, once) == once
    end

    test "Relevance does not exempt a shrunk constructor's surviving argument" do
      # `Relevance.walk`'s `:ctor` clause zipped `args` against the ctor's FULL quantity vector,
      # and `callee_quantities/3` reached the same misalignment through `pad/2`'s
      # `Enum.take(qs, n)`. `Enum.zip/2` truncates silently. By `Erase.erase/2`'s own documented
      # convention a shrunk arg list means the term is ALREADY erased, so its survivor sits in
      # the original TRAILING slot — but the raw zip labelled it with `quantities[0] = :erased`
      # and skipped it. That is the exact false negative Erase's own comment warns about, on the
      # side that is supposed to be Erase's dual.
      env = snat_env()
      ssuc = ctor_atom(env, :ssuc)

      # One argument where the real arity is two, and that argument is the erased binder.
      body = {:ctor, ssuc, [{:var, 0}]}

      assert {:error, {:erased_used_relevantly, _}} =
               Cure.Elab.Relevance.check(env, :probe, [:erased], body)
    end

    test "a saturated constructor still exempts its genuinely erased argument" do
      # Guard against a dual that simply calls everything relevant.
      env = snat_env()
      ssuc = ctor_atom(env, :ssuc)
      present_field = {:ctor, ctor_atom(env, :szero), []}

      body = {:ctor, ssuc, [{:var, 0}, present_field]}

      assert :ok = Cure.Elab.Relevance.check(env, :probe, [:erased], body)
    end
  end
end
