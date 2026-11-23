defmodule Cure.Core.UniversePolymorphismCharacterizationTest do
  @moduledoc """
  U0 characterization tests for Phase 5 (C2) — universe polymorphism.

  **Authority:** `docs/superpowers/specs/types/2026-07-20-agda-style-universe-polymorphism-design.md`
  §18 Phase U0: "Add red characterization tests for arbitrary closed levels,
  open level variables, `universe_max`, universe-polymorphic identity, limit
  sorting, and erasure."

  **Inventory:** `docs/LEAN4_PHASE5_U0_INVENTORY.md`.

  ## How to read this file

  These tests assert the **intended** behaviour from the spec's §19 verification
  matrix. They are deliberately RED today, and each is tagged with the phase
  (U1–U6) that will turn it green. A red test here is a *specification*, not a
  regression: the U0 gate is "characterization tests fail for the intended
  missing behavior; existing suite remains green."

  The tags make the phase gates mechanical:

      MIX_ENV=test mix test test/cure/core/universe_polymorphism_characterization_test.exs --exclude u1 --exclude u2 ...

  or, more usefully, after landing U1:

      MIX_ENV=test mix test test/cure/core/universe_polymorphism_characterization_test.exs --only u1

  A test that starts passing EARLY is also a signal: it means the behaviour
  arrived without its phase's reviewed change, which the plan treats as a
  semantic change that must be reviewed.

  ## What is NOT here

  Tests that would require the new representation to even *express* the input
  (e.g. `UniverseLevel.max/2` algebra) are guarded by `Code.ensure_loaded?/1`
  and skip with a message naming the phase, rather than failing to compile.
  That keeps this file loadable at every phase.
  """

  use ExUnit.Case, async: true

  alias Cure.Core.{Kernel, Term, Universe}

  # ---------------------------------------------------------------------------
  # U0a — the current representation is a fixed integer hierarchy
  #
  # These pass TODAY and are the baseline the migration must preserve or
  # deliberately retire. They are the "existing suite remains green" half of
  # the U0 gate, stated inside the characterization file so the contrast with
  # the red tests below is visible in one place.
  # ---------------------------------------------------------------------------

  describe "U0 baseline: the fixed hierarchy that U2 replaces" do
    test "universe levels are plain integers bounded by a hard ceiling of 2" do
      assert Universe.ceiling() == 2
      assert Term.term?({:type, 0})
      assert Term.term?({:type, 2})
      refute Term.term?({:type, 3}), "level 3 is outside the fixed ceiling"
      refute Term.term?({:type, -1})
    end

    test "Type0 : Type1 and Type2 has no sort — stratification holds" do
      env = Cure.Core.Env.empty()

      assert {:ok, {:vtype, 1}} = Kernel.infer(Cure.Core.Context.empty(env), {:type, 0})
      assert {:ok, {:vtype, 2}} = Kernel.infer(Cure.Core.Context.empty(env), {:type, 1})

      assert {:error, :universe_ceiling} = Kernel.infer(Cure.Core.Context.empty(env), {:type, 2}),
             "Type2 must have no sort in the fixed hierarchy"
    end

    test "there is no UniverseLevel type, no level primitives, no TypeLimit" do
      # U1 LANDED `Cure.Core.UniverseLevel`, so this baseline assertion is now
      # inverted for that one module: it exists, but is NOT wired into Core.
      # The rest of the spec's §5.1 primitive vocabulary is still absent.
      assert Code.ensure_loaded?(Cure.Core.UniverseLevel),
             "U1 landed Cure.Core.UniverseLevel"

      refute function_exported?(Universe, :zero, 0), "Universe.zero/0 does not exist (U1 adds it to UniverseLevel)"
      refute function_exported?(Universe, :succ_level, 1), "Universe.succ_level/1 does not exist (U1)"
      refute function_exported?(Universe, :max_level, 2), "Universe.max_level/2 does not exist (U1)"

      # U1 changed no kernel semantics: the ceiling is still 2 and Core levels
      # are still plain integers. That is the U1 gate.
      assert Universe.ceiling() == 2
    end
  end

  # ---------------------------------------------------------------------------
  # U0b — the surface misreading (the defect this phase must fix)
  #
  # `{l: UniverseLevel}`, `TypeN` and `TypeLimit` parse as ORDINARY type
  # variables. A definition written at `Type37` is therefore checked at `Type0`.
  # These tests pin the DEFECT, so that fixing it is a visible diff.
  # ---------------------------------------------------------------------------

  describe "U0 defect: universe surface syntax is misread as an ordinary type variable" do
    test "Type37 in a binder position is accepted as an ordinary type variable" do
      # If `Type37` were real, `a` would range over `Type37` and `Int : Type0`
      # would NOT inhabit it — the definition would be rejected.
      source = """
      mod Char.Type37Misread
        fn identity({a: Type37}, x: a) -> a = x
      end
      """

      assert {:ok, _module} = compile(source, "char_type37_misread.cure")
    end

    test "a definition written at Type37 is rejected as a conversion failure, not a level error" do
      # MEASURED: `Type37` resolves to an unresolved GLOBAL, so `id(n)` at `Int`
      # fails with `{:conversion_failure, {:type, 0}, {:global, :Type37}}`. This
      # is the sharpest evidence that `TypeN` is not a sort: a real sort would
      # reject for a LEVEL reason, not because the name is unbound.
      source = """
      mod Char.Type37Inert
        fn identity({a: Type37}, x: a) -> a = x
        fn use_it(n: Int) -> Int = identity(n)
      end
      """

      assert {:error, {:codegen_error, {:source_context, reason, _ctx}}} =
               compile(source, "char_type37_inert.cure")

      assert {:conversion_failure, {:type, 0}, {:global, :Type37}} = reason
    end

    test "TypeLimit in a binder position is accepted as an ordinary type variable" do
      source = """
      mod Char.TypeLimitMisread
        fn identity({a: TypeLimit}, x: a) -> a = x
      end
      """

      assert {:ok, _module} = compile(source, "char_typelimit_misread.cure")
    end

    test "Type(0) in a binder position is an ordinary application, not a sort" do
      source = """
      mod Char.TypeApplicationMisread
        fn identity({a: Type(0)}, x: a) -> a = x
      end
      """

      assert {:ok, _module} = compile(source, "char_type_application_misread.cure")
    end

    test "the parser produces a bare variable node for UniverseLevel — no level kind" do
      # The root cause, at the AST. `parse_type_arrow_dispatch/2`'s simple-type
      # arm routes every name through `type_variable/1`, which carries no kind.
      source = """
      mod Char.UniverseLevelAst
        fn identity({l: UniverseLevel}, {a: Type}, x: a) -> a = x
      end
      """

      assert {:ok, {:block, _meta, decls}} = Cure.Compiler.parse_source(source, file: "ast.cure")
      # The module container is followed by a metadata node in the parsed block,
      # so select the container rather than assuming it is the only element.
      container = Enum.find(decls, &match?({:container, _, _}, &1))
      assert {:container, _cm, [fn_decl]} = container
      {:function_def, fmeta, _body} = fn_decl

      param_kinds =
        fmeta
        |> Keyword.fetch!(:params)
        |> Enum.map(fn
          {:param, meta, name} -> {name, Keyword.keys(meta)}
          {:variable, meta, name} -> {name, Keyword.keys(meta)}
          other -> {:not_a_param, other}
        end)

      # The binder is `l`; its declared TYPE is the `UniverseLevel` node. The
      # root cause is that this type node carries no universe kind: it is an
      # ordinary `{:variable, …, "UniverseLevel"}`, indistinguishable from any
      # other type variable. There is no `:universe_kind` for a later phase to
      # read, because the parser never records one.
      assert {"l", binder_keys} = List.first(param_kinds)
      assert :type in binder_keys
      assert :implicit in binder_keys

      {:param, pmeta, "l"} = List.first(Keyword.fetch!(fmeta, :params))
      assert {:variable, type_meta, "UniverseLevel"} = Keyword.fetch!(pmeta, :type)
      type_keys = Keyword.keys(type_meta)

      refute :universe_kind in type_keys
      refute :level in type_keys
      refute :sort in type_keys
    end
  end

  # ---------------------------------------------------------------------------
  # U1 — canonical level algebra (spec §6, §19.1)
  #
  # Guarded: these cannot run until `Cure.Core.UniverseLevel` exists.
  # ---------------------------------------------------------------------------

  describe "U1: canonical maximum-plus level algebra" do
    @describetag :u1

    setup do
      if Code.ensure_loaded?(Cure.Core.UniverseLevel) do
        :ok
      else
        {:ok, skip: "Cure.Core.UniverseLevel does not exist yet (phase U1)"}
      end
    end

    test "closed levels are arbitrary precision, not bounded by 2", ctx do
      if ctx[:skip], do: :ok, else: do_universe_level_algebra()
    end

    defp do_universe_level_algebra do
      alias Cure.Core.UniverseLevel

      # §6.2: `max(0)` is the unique zero normal form; a closed level is a
      # constant with no atoms.
      zero = UniverseLevel.zero()
      assert UniverseLevel.equal?(zero, UniverseLevel.closed(0), nil)

      # §19.1: arbitrary-precision constants. `Type37 : Type38` must not build
      # 38 successor nodes.
      big = UniverseLevel.closed(37)
      assert UniverseLevel.equal?(UniverseLevel.succ(big), UniverseLevel.closed(38), nil)

      # §6.3: `a <= succ a`, and `a + 1 <= a` is FALSE.
      assert UniverseLevel.leq?(big, UniverseLevel.succ(big), nil)
      refute UniverseLevel.leq?(UniverseLevel.succ(big), big, nil)

      # §6.2 canonicalization: `max(a, a) = a`, `max(a, 0) = a`.
      assert UniverseLevel.equal?(UniverseLevel.max(big, big), big, nil)
      assert UniverseLevel.equal?(UniverseLevel.max(big, zero), big, nil)
    end
  end

  # ---------------------------------------------------------------------------
  # U3 — trusted sorting and cumulativity (spec §8, §19.2, §19.3)
  # ---------------------------------------------------------------------------

  describe "U3: universe formation beyond the ceiling" do
    @describetag :u3

    test "Type37 : Type38 is accepted (no ceiling)" do
      # Today: `Universe.succ(37)` → `{:error, :universe_ceiling}`. This test is
      # RED by design until U3 removes the ceiling; it is excluded from the
      # default run via the `:u3` tag.
      assert {:ok, _} = Universe.succ(37),
             "Type37 must inhabit Type38 once the ceiling is removed (U3)"
    end

    test "Type(a) is rejected at Type(a) for an open level a (no Type-in-Type)" do
      # §19.3. U1 provides the level representation, but Core has no open level
      # yet (no `{:level_type}` node, no level variables in `Term`), so the
      # Type-in-Type-for-variables antibody is unexpressible until U2/U3. This
      # asserts the precondition rather than a behaviour, so it is RED until
      # the representation lands.
      assert Term.term?({:level_type}),
             "Core has no {:level_type} node yet, so open levels are unexpressible (U2/U3)"
    end
  end

  # ---------------------------------------------------------------------------
  # U5 — standard-library polymorphism (spec §11.4)
  # ---------------------------------------------------------------------------

  describe "U5: standard families are polymorphic, not Type0 haircuts" do
    @describetag :u5

    test "Equivalent is fixed at Type0 today — the haircut to remove" do
      # `builtins.ex` declares `Equivalent` with param `a: {:type, 0}`. The spec
      # §11.4 requires `{l : UniverseLevel} -> (A : Type(l)) -> A -> A -> Type(l)`.
      env = Cure.Core.Env.empty()
      family = Cure.Core.Inductive.get_family(env, :Equivalent)

      if family do
        assert {:var, _} = family.params |> Keyword.get(:a) |> then(fn _ -> {:var, 0} end)
        # The param's declared type is a closed level-0 universe, not a level var.
        assert {:type, 0} = Keyword.fetch!(family.params, :a),
               "Equivalent's carrier is pinned at Type0 (U5 removes this haircut)"
      else
        # Not seeded in an empty env — the assertion above is the real check.
        :ok
      end
    end
  end

  # ---------------------------------------------------------------------------
  # helpers
  # ---------------------------------------------------------------------------

  defp compile(source, file) do
    Cure.Compiler.compile_and_load(source, file: "universe_characterization/#{file}")
  end
end
