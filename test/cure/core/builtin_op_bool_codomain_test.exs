defmodule Cure.Core.BuiltinOpBoolCodomainTest do
  @moduledoc """
  `Builtins.seed_ops/1` computes ONE `bool_ty` and bakes it as the codomain of all 12 comparison
  ops and both structural-equality ops. Its own doc says it must "Run AFTER the inductive seeds
  so the Bool codomain resolves through the registry" — and `seed/2` does run it last. But the
  value is a snapshot, a plain Core term, not a live lookup, so it has to be right at that
  instant.

  It was not, in exactly the scenario the doc describes. `seed/2` takes an `exclude` set, and
  every real call site threads it from the compiled module's own `declared_type_names/1`. A
  module that declares a type named `Bool` — `lib/std/bool.cure`, the module that DEFINES the
  canonical Bool, and any user module that merely names a local type `Bool` — therefore has
  `:Bool` excluded, `maybe_seed(:bool, …)` registers nothing, and `Inductive.builtin(env, :bool)`
  is still `nil` when `seed_ops/1` reads it. The module's own `@builtin(:bool)` declaration
  registers the real family later, in `elaborate_declarations`, long after the snapshot closed
  over `{:data, nil, [], []}`.

  The consequence reaches the kernel. `Kernel.infer(ctx, {:data, nil, _, _})` looks the family up
  with a bare `Map.get`, gets `nil`, and reports `{:error, {:unknown_family, nil}}`. That
  propagates unmodified up to `check_def/2`'s builtin-op clause, whose comment promises those ops
  are "Total by fiat (Lean/Idris treat primitive ops so)". In the one real scenario, they weren't.

  `maybe_seed/5` excludes precisely on `family.name`, so the family the module goes on to declare
  carries the same name the seed would have used. The canonical name is the correct snapshot
  under both orders — which is the property below: an op's signature never varies with what else
  got seeded first. Lean's kernel Nat/Bool primitives and Agda's BUILTIN pragmas resolve once,
  unconditionally, never as a function of seeding order.

  Checkability is a separate question and stays honest: in an env where `Bool` was excluded and
  never subsequently declared, `int_lt : Int -> Int -> Bool` genuinely cannot check, and
  `check_def/2` says so. What must hold is that once the module's own Bool IS registered — the
  real `elaborate_declarations` order — the op checks.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Env, Inductive, Kernel}

  defp with_own_bool(env) do
    family = Inductive.family(:"Std.Bool#Bool", [], [], 0)
    ctors = [Inductive.ctor(:"Std.Bool#False", [], []), Inductive.ctor(:"Std.Bool#True", [], [])]

    env |> Inductive.declare(family, ctors) |> Inductive.register_builtin(:bool, :"Std.Bool#Bool")
  end

  test "a comparison op's codomain names the real Bool family even when :bool is excluded" do
    env = Builtins.seed(Env.empty(), MapSet.new([:Bool]))

    assert %{type: {:pi, _g1, _, {:pi, _g2, _, {:data, fam, [], []}}}} = Env.get_def(env, :int_lt)
    refute is_nil(fam)
    assert fam == :"Std.Bool#Bool"
  end

  test "struct_eq/struct_ne's codomain does too — same snapshot, same defect" do
    env = Builtins.seed(Env.empty(), MapSet.new([:Bool]))

    for op <- [:struct_eq, :struct_ne] do
      assert %{type: {:pi, _g1, _, {:pi, _g2, _, {:pi, _g3, _, {:data, fam, [], []}}}}} = Env.get_def(env, op)
      assert fam == :"Std.Bool#Bool"
    end
  end

  test "an op's signature does not vary with what else got seeded first" do
    seeded = Builtins.seed(Env.empty())
    excluded = Builtins.seed(Env.empty(), MapSet.new([:Bool]))

    for op <- [:int_lt, :int_ge, :float_eq, :struct_eq, :struct_ne] do
      assert Env.get_def(seeded, op).type == Env.get_def(excluded, op).type
    end
  end

  test "the real pipeline order leaves the ops checkable" do
    # `program.ex` excludes :Bool from `Builtins.seed`, then `elaborate_declarations` processes
    # the module's own `@builtin(:bool)` — which is `Inductive.declare/3` +
    # `register_builtin/3` for :Bool under key :bool, the same primitives `builtins.ex` uses.
    env = Env.empty() |> Builtins.seed(MapSet.new([:Bool])) |> with_own_bool()

    assert Inductive.builtin(env, :bool) == :"Std.Bool#Bool"
    assert :ok = Kernel.check_def(env, :int_lt)
    assert :ok = Kernel.check_def(env, :struct_eq)
  end

  test "and the ordinary order — Bool seeded programmatically — still checks" do
    env = Builtins.seed(Env.empty())

    assert :ok = Kernel.check_def(env, :int_lt)
    assert :ok = Kernel.check_def(env, :struct_eq)
  end

  test "an env whose Bool is excluded and never declared reports the missing family" do
    # Not a defect: the env is genuinely incomplete. What matters is that it names the canonical
    # Bool family rather than nil, so the diagnostic points at the family that is actually absent.
    env = Builtins.seed(Env.empty(), MapSet.new([:Bool]))

    assert {:error, {:unknown_family, :"Std.Bool#Bool"}} = Kernel.check_def(env, :int_lt)
  end
end
