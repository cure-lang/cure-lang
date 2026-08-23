defmodule Antigen.Assays.ElabSoundnessTest do
  use ExUnit.Case, async: true
  alias Antigen.{Assays.Elab, Challenge}
  alias Cure.Core.{Env, Builtins}

  @bool {:data, :"Std.Bool#Bool", [], []}
  @nat {:data, :"Std.Nat#Nat", [], []}

  defp prog(src),
    do:
      Challenge.new(
        kind: :elab_program,
        assay: "elab/soundness",
        label: :well_typed,
        payload: %{id: 1, src: src},
        seed: 1
      )

  # A seeded env (Bool/Nat families present) so infer/eval resolve @bool/@nat.
  # NOTE: `Builtins.seed/2`'s 2nd arg is a MapSet (families to SKIP seeding),
  # not a list — `seed(Env.empty(), [])` crashes `MapSet.member?/2` with
  # FunctionClauseError (verified). Call the 1-arity form (uses the `MapSet.new()`
  # default) so every test below actually reaches the assay instead of crashing
  # in the fixture.
  defp seeded, do: Builtins.seed(Env.empty())

  # An op-map identical to @real_kernel EXCEPT `elaborate`, which returns a
  # synthetic env — the only way to feed the decision procedure a chosen env.defs.
  defp kernel_with_env(env) do
    %{
      elaborate: fn _src -> {:ok, env} end,
      infer: &Cure.Core.Kernel.infer/2,
      check: &Cure.Core.Kernel.check/3,
      conv: &Cure.Core.Conv.conv_values?/4,
      eval: &Cure.Core.Eval.eval/2
    }
  end

  test "baseline: a genuinely well-typed program re-checks sound (:ok)" do
    # id : Nat -> Nat = fn x -> x ; emitted core body {:lam, Cure.Core.Grade.unrestricted(),Nat,{:var,0}} infers cleanly.
    assert Elab.run(prog("mod P\nfn id(x: Nat) -> Nat = x\nend")) == :ok
  end

  test "type_annotation_wrong: body checkable but at a different type" do
    # def `bad`: body is Bool->Bool identity, DECLARED Nat->Nat. infer=vpi Bool Bool,
    # eval(declared)=vpi Nat Nat -> not convertible -> type_annotation_wrong.
    env =
      seeded()
      |> Env.add_def(
        :bad,
        {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat},
        {:lam, Cure.Core.Grade.unrestricted(), @bool, {:var, 0}}
      )

    assert {:violation, {:type_annotation_wrong, :bad, _}} =
             Elab.run(prog("ignored"), kernel_with_env(env))
  end

  test "reject is NOT a V3 infection (belongs to elab/completeness)" do
    # A program the elaborator rejects -> {:error,_} from elaborate -> :ok here.
    assert Elab.run(prog("mod P\nfn oops(x: Nat) -> Nat = nonexistent_fn(x)\nend")) == :ok
  end

  test "elaborator crash is an infection" do
    k = %{
      elaborate: fn _ -> raise "boom" end,
      infer: &Cure.Core.Kernel.infer/2,
      check: &Cure.Core.Kernel.check/3,
      conv: &Cure.Core.Conv.conv_values?/4,
      eval: &Cure.Core.Eval.eval/2
    }

    assert {:violation, {:elaborator_raised, 1, _}} = Elab.run(prog("x"), k)
  end

  test "hole-bearing def is skipped, not infected" do
    # body has a hole; kernel would accept, but we skip it -> whole run :ok.
    env =
      seeded()
      |> Env.add_def(
        :h,
        {:pi, Cure.Core.Grade.unrestricted(), @nat, @nat},
        {:lam, Cure.Core.Grade.unrestricted(), @nat, {:hole, :g}}
      )

    assert Elab.run(prog("ignored"), kernel_with_env(env)) == :ok
  end

  test "run/2 with the real op-map is byte-identical to run/1" do
    c = prog("mod P\nfn id(x: Nat) -> Nat = x\nend")
    assert Elab.run(c) == Elab.run(c, Elab.__real_kernel__())
  end

  describe "constructor bodies (checking-mode fallback)" do
    # `Option(T)` is parameter-bearing; `Some(v)` bodies are inferable only in
    # checking mode. Kernel.infer returns {:error, {:ctor_requires_checking_mode, _}}.
    # Build the family + a sound and an unsound def directly in a seeded env.
    defp option_env do
      # A minimal parameter-bearing family F(a: Type) with ctor Mk(x: a) : F(a).
      #
      # Two details are load-bearing, verified against Kernel.check's `{:ctor,...}`
      # clause (which re-derives `actual = {:vdata, family, actual_params ++
      # actual_indices}` from `result_params`/`result_indices` and Conv-compares it
      # to the expected `{:vdata,...}}`):
      #   1. `declare/3`'s 3rd arg is `[ctor()]` (a LIST) — `declare(fam, ctor)`
      #      (bare map) makes `Enum.reduce` inside `declare/3` iterate the ctor
      #      MAP's `{key, value}` pairs instead of the ctor itself, crashing with
      #      MatchError on `%{name: cname} = c`.
      #   2. `result_params` must be `[{:var, 1}]` (mirrors Kernel's own
      #      `check_uniform_params/5` formula `{:var, num_args + (num_params - 1 -
      #      p)}` for Mk's 1 arg / F's 1 param), NOT `[]`. With `[]`, `check/3`
      #      re-derives `actual = {:vdata, :F, []}` (param dropped) instead of
      #      `{:vdata, :F, [Nat]}`, so `Conv.conv_values?`'s spine-length check
      #      fails `conv_spine?` even for the intentionally-SOUND `ok_mk` case
      #      below (0-length actual spine vs 1-length expected) — the "sound"
      #      test would falsely report a `{:core_ill_typed, ...}}` violation
      #      instead of `:ok`.
      fam = Cure.Core.Inductive.family(:F, [{:a, {:type, 0}}], [], 0)
      ctor = Cure.Core.Inductive.ctor(:Mk, [{:x, {:var, 0}}], [], [:unrestricted], [{:var, 1}])
      seeded() |> Cure.Core.Inductive.declare(fam, [ctor])
    end

    test "sound parameter-bearing constructor body re-checks :ok (uses check, not infer)" do
      # def ok_mk : F(Nat) = Mk(Z)   — well typed; infer alone would misreport it.
      env =
        option_env()
        |> Env.add_def(:ok_mk, {:data, :F, [@nat], []}, {:ctor, :Mk, [{:ctor, :"Std.Nat#Z", []}]})

      assert Elab.run(prog("ignored"), kernel_with_env(env)) == :ok
    end

    test "mismatched constructor body still infects" do
      # def bad_mk : F(Bool) = Mk(Z)  — Z:Nat, but F(Bool) expects x:Bool -> reject.
      env =
        option_env()
        |> Env.add_def(:bad_mk, {:data, :F, [@bool], []}, {:ctor, :Mk, [{:ctor, :"Std.Nat#Z", []}]})

      assert {:violation, {:core_ill_typed, :bad_mk, _}} =
               Elab.run(prog("ignored"), kernel_with_env(env))
    end

    # Antibody for the kernel change "whnf the GOAL in check/3's `{:ctor,…}` clause"
    # (kernel.ex ~260): a constructor may be checked against any type that δ-unfolds
    # to the family's `{:vdata,…}` — e.g. a `typealias`/alias-def goal, which reaches
    # `check/3` as the bare alias global (a NEUTRAL), not a literal `{:vdata,…}`. The
    # goal type of each def below is `{:global, :FNatAlias}` / `{:global, :FBoolAlias}`;
    # `Eval.eval` produces the `{:nglobal,…}` neutral (eval never δ-unfolds a def), so
    # only `check`'s own `whnf_value` exposes the `{:vdata}` head. Both aliases are
    # `certify`'d so `Normalise.whnf_value` will δ-unfold them (see normalise.ex:243).
    #
    # The pair is the antibody: COMPLETENESS — a SOUND ctor at an alias goal is admitted
    # (was a false `:core_ill_typed` via the infer→CRCM fallback before the whnf); and
    # SOUNDNESS — an UNSOUND ctor at an alias goal is STILL rejected, proving the whnf
    # exposes the head WITHOUT admitting a constructor the un-aliased goal would reject
    # (whnf(alias) is definitionally the alias, so no distinct normal forms are equated).
    defp aliased_option_env do
      option_env()
      |> Env.add_def(:FNatAlias, {:type, 0}, {:data, :F, [@nat], []})
      |> Env.certify(:FNatAlias)
      |> Env.add_def(:FBoolAlias, {:type, 0}, {:data, :F, [@bool], []})
      |> Env.certify(:FBoolAlias)
    end

    test "COMPLETENESS: sound ctor body at a δ-reducible ALIAS goal re-checks :ok" do
      # def ok_alias : FNatAlias = Mk(Z)  where FNatAlias := F(Nat).
      env =
        aliased_option_env()
        |> Env.add_def(:ok_alias, {:global, :FNatAlias}, {:ctor, :Mk, [{:ctor, :"Std.Nat#Z", []}]})

      assert Elab.run(prog("ignored"), kernel_with_env(env)) == :ok
    end

    test "SOUNDNESS: unsound ctor body at a δ-reducible ALIAS goal STILL infects" do
      # def bad_alias : FBoolAlias = Mk(Z)  where FBoolAlias := F(Bool); Z:Nat ≠ Bool.
      env =
        aliased_option_env()
        |> Env.add_def(:bad_alias, {:global, :FBoolAlias}, {:ctor, :Mk, [{:ctor, :"Std.Nat#Z", []}]})

      assert {:violation, {:core_ill_typed, :bad_alias, _}} =
               Elab.run(prog("ignored"), kernel_with_env(env))
    end
  end

  describe "fuel bound" do
    # A certified, non-normalizing global (`loop`'s body is a bare self-reference
    # `{:global, :loop}` — NOT an application). We certify it directly (bypassing
    # the totality checker that would normally block it) — the assay must NOT
    # assume elaboration prevents a non-normalizing emitted def.
    #
    # `loop`'s OWN check_one pass is deliberately clean (infer only ever reads a
    # global's DECLARED type — `infer(ctx,{:global,:loop})` = eval(@nat) = Nat,
    # matching its own declared `@nat`, no δ needed — so `:loop` itself is not
    # what infects). A second def, `probe`, is what forces δ: its declared type
    # is `Eq(Nat, loop, Z)` (an endpoint IS `loop`), and its body is `refl(Z)`.
    # Checking `probe` compares `inferred = Eq(Nat, Z, Z)` against `declared =
    # Eq(Nat, loop, Z)`; the middle endpoints (`Z` vs `loop`) are not both
    # neutral, so Conv falls to the general path, which `Normalise.whnf_value`s
    # BOTH sides — forcing the `{:nglobal, :loop}` neutral to δ-unfold.
    #
    # The normalizer detects that δ reproduces the identical neutral and
    # freezes it immediately. The probe is therefore rejected as a structured
    # conversion failure without waiting for a fuel timeout.
    test "non-normalizing emitted def is rejected without hanging" do
      env =
        seeded()
        |> Env.add_def(:loop, @nat, {:global, :loop})
        |> Env.certify(:loop)
        |> Env.add_def(
          :probe,
          {:data, :"Std.Equivalent#Equivalent", [@nat], [{:global, :loop}, {:ctor, :"Std.Nat#Z", []}]},
          {:ctor, :"Std.Equivalent#reflexive", [{:ctor, :"Std.Nat#Z", []}]}
        )

      task = Task.async(fn -> Elab.run(prog("ignored"), kernel_with_env(env)) end)
      assert {:violation, {:core_ill_typed, :probe, {:conversion_failure, _, _}}} =
               Task.await(task, 30_000)
    end
  end

  describe "generator + runner wiring" do
    alias Antigen.Generators.ElabComplete
    alias Antigen.Runner

    test "soundness_challenges re-tags the completeness catalog" do
      cs = ElabComplete.soundness_challenges()
      assert cs != []
      assert Enum.all?(cs, fn c -> c.kind == :elab_program and c.assay == "elab/soundness" end)
      # same programs as completeness (same ids), only the assay tag differs
      assert Enum.map(cs, & &1.payload.id) ==
               Enum.map(ElabComplete.completeness_challenges(), & &1.payload.id)
    end

    test "runner dispatches elab/soundness to the Elab assay (replay_one)" do
      [c | _] = ElabComplete.soundness_challenges()
      # every catalog program is construction-guaranteed well-typed -> sound
      assert Runner.replay_one(c) == :ok
    end

    test "the whole soundness catalog re-checks clean under the real kernel" do
      assert Enum.all?(ElabComplete.soundness_challenges(), fn c ->
               Runner.replay_one(c) == :ok
             end)
    end
  end
end
