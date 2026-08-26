defmodule Cure.Core.Builtins do
  alias Cure.Core.Grade

  @moduledoc """
  Canonical builtin-inductive schemas and the programmatic seeder.

  Schema validation checks constructor NAMES and arities, not arity alone:
  the literal wiring (true/false -> True/False) and erasure atom mapping
  (False/True -> false/true; Z/S -> int) key off these exact names, so a
  shape-conformant but name-mismatched binding (e.g. `Coin = Heads | Tails`
  tagged `@builtin(:bool)`) is a real miscompile risk and must be rejected.
  """
  alias Cure.Core.{Env, Inductive}

  # key => list of {ctor_name, arity}. Names are load-bearing.
  @schemas %{
    any: [],
    bool: [{:False, 0}, {:True, 0}],
    nat: [{:Z, 0}, {:S, 1}],
    eq: [{:reflexive, 1}],
    sigma: [{:mk_pair, 2}],
    list: [{:Nil, 0}, {:Cons, 2}],
    # First/Next each carry an erased implicit index binder `{m : Nat}` (like
    # Equivalent's erased witness `w`), so their STORED arities are 1 and 2 —
    # First: {m}; Next: {m}, Bounded(m). The erased `m` drops at emit, leaving
    # the runtime shape First->0 / Next(pred)->pred+1 (Nat's Z/S erasure).
    bounded: [{:First, 1}, {:Next, 2}],
    # Int : Type0 = FromNat(Nat) | NegativeSuccessor(Nat). Both constructors are
    # 1-ary (each field is a Nat), so — unlike Nat's Z/S — arity cannot
    # disambiguate them; every literal/erasure hook that keys off Int is
    # NAME-keyed, not arity-keyed. FromNat(n) = n; NegativeSuccessor(n) = -(n+1).
    int: [{:FromNat, 1}, {:NegativeSuccessor, 1}],
    # `Char` is a NOMINAL carrier with no constructors — Agda's `BUILTIN CHAR`,
    # not a `Bounded(0x110000)` synonym. Its canonical values are the compact
    # `{:bounded_lit, k}` code points admitted by the kernel's checking rule, so
    # a character literal is still a compile-time value a pattern can match; the
    # empty schema is what says "no ctor may introduce one". Registering the key
    # is how the kernel and the elaborator agree on WHICH family that rule names,
    # since the carrier lives in `Std.Char` and the kernel seeds no `Char`.
    char: []
  }

  # Builtin arithmetic/comparison op globals (K2 wave, spec 2026-07-09). Each is
  # a BODY-LESS def carrying a `builtin_op` marker; the certified-δ engine folds
  # a saturated literal spine via the audited `Eval.fold` table (Lean reduce_nat
  # / Idris Builtin-op analog). Monomorphic per-type (Lean-aligned): the
  # elaborator type-directs `+`/`==`/… to the int_* or float_* twin. `{name,
  # op_key}`. Comparisons (@cmp_ops) have a Bool codomain; arithmetic/neg return
  # the operand type. int_rem is Int-only (no float_rem — matches infer_prim).
  @cmp_ops [:lt, :le, :gt, :ge, :eq, :ne]

  @int_binops [
    {:int_add, :add},
    {:int_sub, :sub},
    {:int_mul, :mul},
    {:int_div, :div},
    {:int_rem, :rem},
    {:int_lt, :lt},
    {:int_le, :le},
    {:int_gt, :gt},
    {:int_ge, :ge},
    {:int_eq, :eq},
    {:int_ne, :ne},
    # Int-only bitwise (no float twin). Codomain is Int (not in @cmp_ops).
    {:int_band, :band},
    {:int_bor, :bor},
    {:int_bxor, :bxor},
    {:int_bsl, :bsl},
    {:int_bsr, :bsr}
  ]

  # NOTE `float_div` carries its OWN op key `:fdiv`, not `:div`. The op key is what
  # `Eval.fold/2` and `Emit.erl_binop/1` dispatch on, and Erlang's `div` is INTEGER
  # division (`7.0 div 2.0` raises badarith) while `/` is float division. `add`/`sub`/
  # `mul` and the comparisons can safely share a key with their int twins because the
  # corresponding BEAM operators (`+ - * < =< > >= == /=`) are int/float polymorphic;
  # division is the sole operator where they are NOT the same instruction.
  @float_binops [
    {:float_add, :add},
    {:float_sub, :sub},
    {:float_mul, :mul},
    {:float_div, :fdiv},
    {:float_lt, :lt},
    {:float_le, :le},
    {:float_gt, :gt},
    {:float_ge, :ge},
    {:float_eq, :eq},
    {:float_ne, :ne}
  ]

  @int_unops [{:int_neg, :neg}, {:int_bnot, :bnot}]
  @float_unops [{:float_neg, :neg}]

  # Amendment A1 (spec §1-A): polymorphic STRUCTURAL equality —
  # struct_eq/struct_ne : Pi(a: Type0). a -> a -> Bool (explicit ω-present type
  # argument; emit drops it). Transitional representation of the retiring
  # {:prim, :eq/:ne} on non-int/float/bool operands: the hook folds only two
  # literal VALUE args (late-instantiated polymorphic operands), stays NEUTRAL
  # on ADTs (R8c). Distinct marker atoms so hook/emit/lint never conflate them
  # with the monomorphic :eq/:ne. Op set is therefore 25, not 23.
  @struct_ops [{:struct_eq, :struct_eq}, {:struct_ne, :struct_ne}]

  @doc "The expected schema descriptor for a builtin key. Raises for an unknown key."
  @spec schema(atom()) :: [{atom(), non_neg_integer()}]
  def schema(key), do: Map.fetch!(@schemas, key)

  @doc """
  Validate that `family_id` in `env` conforms to `key`'s canonical schema —
  by constructor NAME and arity (not arity alone). `:ok` or raises `ArgumentError`.
  """
  @spec validate!(Env.t(), atom(), atom()) :: :ok
  def validate!(%Env{} = env, key, family_id) do
    expected =
      schema(key)
      |> Enum.map(fn {name, arity} -> {Atom.to_string(name), arity} end)
      |> Enum.sort()

    ctors = Inductive.ctors_of(env, family_id) || []

    actual =
      ctors
      |> Enum.map(fn c -> {Cure.Elab.Name.base(c.name), length(Map.get(c, :args, []))} end)
      |> Enum.sort()

    if actual == expected do
      :ok
    else
      raise ArgumentError,
            "@builtin(#{inspect(key)}) on #{inspect(family_id)}: expected constructors " <>
              "#{inspect(expected)} (name and arity), got #{inspect(actual)}"
    end
  end

  @doc """
  The modules the kernel itself provides.

  These have no source file and never appear in a manifest, but a module may
  name them: they are owners of seeded globals, not of anything compiled. The
  set is derived from what `seed/2` actually installs rather than listed, so a
  builtin cannot become referable without also becoming provided.
  """
  @spec provided_modules() :: [String.t()]
  def provided_modules do
    Env.empty()
    |> seed(MapSet.new())
    |> Map.fetch!(:defs)
    |> Map.keys()
    |> Enum.map(&Cure.Elab.Name.owner/1)
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
    |> Enum.sort()
  end

  @doc """
  Seed an env with the canonical `Bool` (`False | True`) and `Nat` (`Z | S(Nat)`)
  families, each validated against its schema and registered under its builtin
  key. This is the base env for kernel unit tests and the conformance harness
  (the prelude compile obtains the same families via its `@builtin` declarations;
  Task 4 pins the two representations equal).
  """
  @spec seed(Env.t(), MapSet.t()) :: Env.t()
  def seed(%Env{} = env, exclude \\ MapSet.new()) do
    env
    |> seed_builtin(:any, exclude)
    |> seed_builtin(:bool, exclude)
    |> seed_builtin(:nat, exclude)
    |> seed_builtin(:int, exclude)
    |> seed_builtin(:eq, exclude)
    |> seed_builtin(:sigma, exclude)
    |> seed_builtin(:list, exclude)
    |> seed_ops()
    |> seed_primitives()
  end

  # The machine base types' name→node floor (spec 2026-07-10-primitive-type-
  # declarations). These are the canonical bindings the Std `@builtin(:tag)
  # primitive Name` declarations mirror and confirm. Inert w.r.t. the kernel:
  # a surface-name resolution table only, adding no Core node and changing no
  # judgement (the three nodes predate it, gated by the #2/#3 batch).
  defp seed_primitives(%Env{} = env) do
    # `Int` is NO LONGER a primitive: it is the inductive `@builtin(:int)` family
    # (FromNat/NegativeSuccessor), seeded by `seed_builtin(:int)` and resolving
    # exactly as `Nat` does. Removing the primitive binding lets every
    # `Env.primitive(env, "Int")` site fall through to family lookup (spec
    # 2026-07-18-inductive-int §3a). Float/Binary/Atom stay primitive.
    env
    |> Env.put_primitive("Float", {:float_type})
    |> Env.put_primitive("Binary", {:binary_type})
    |> Env.put_primitive("Atom", {:atom_type})
  end

  @doc """
  Seed the 32 builtin-op globals (16 int binary [11 arith/cmp + 5 bitwise] +
  10 float binary + int_neg/int_bnot/float_neg + the A1 polymorphic
  struct_eq/struct_ne) as body-less defs carrying a `builtin_op` marker. Public
  so the Antigen generator envs (SigMenu v1, Generators.Totality) can reuse it.
  Run AFTER the inductive seeds so the Bool codomain resolves through the
  registry.
  """
  @spec seed_ops(Env.t()) :: Env.t()
  def seed_ops(%Env{} = env) do
    bool_ty = {:data, bool_family_id(env), [], []}
    int_ty = {:data, int_family_id(env), [], []}

    env
    |> seed_binops(@int_binops, int_ty, bool_ty)
    |> seed_binops(@float_binops, {:float_type}, bool_ty)
    |> seed_unops(@int_unops, int_ty)
    |> seed_unops(@float_unops, {:float_type})
    |> seed_struct_ops(bool_ty)
    |> seed_run()
  end

  # `run : {a : Type} -> Effect(a) -> a` executes a direct-style effect value.
  # It is an ordinary function at the language level: the type parameter is
  # erased, and the emitter lowers the call to its sole present argument.
  defp seed_run(env) do
    ty =
      {:pi, :erased, {:type, 0}, {:pi, Grade.unrestricted(), {:effect_type, {:var, 0}}, {:var, 1}}}

    env
    |> Env.add_def(:run, ty, nil, [:erased, :unrestricted])
    |> Env.register_builtin_op(:run, :effect_run)
  end

  # The family id to bake into every comparison / structural-equality codomain.
  #
  # `seed_ops/1` snapshots this as a plain Core term, not a live registry lookup, so it has to
  # be right at the moment it runs — and `seed/2` runs it unconditionally, as its last step.
  # Reading it only out of `Inductive.builtin(env, :bool)` got `nil` in exactly the scenario
  # `seed_ops`'s own doc describes: a module that declares its own `Bool` has `:Bool` in
  # `seed/2`'s `exclude` set, so `maybe_seed(:bool, …)` never registered anything, and the
  # module's `@builtin(:bool)` declaration only registers the real family LATER, in
  # `elaborate_declarations`. All 12 comparison ops and both struct ops were left with
  # `{:data, nil, [], []}` as their codomain — a type `Kernel.infer/2` rejects with
  # `{:error, {:unknown_family, nil}}`, which propagates to `check_def/2`'s builtin-op clause
  # whose own comment promises those ops are "Total by fiat".
  #
  # `maybe_seed/5` excludes precisely on `family.name`, so the family the module goes on to
  # declare carries the same name the seed would have used. The canonical name is therefore the
  # correct snapshot under both orders, and the op signatures no longer vary with seeding order.
  defp bool_family_id(env),
    do: Inductive.builtin(env, :bool) || bool_family(Env.with_owner(env, "Std.Bool")).name

  # Int is now the inductive family Std.Int#Int (FromNat | NegativeSuccessor); the
  # primitive-arithmetic operators (@int_binops/@int_unops) take it as their operand
  # domain. Mirrors bool_family_id/1's canonical-name snapshot under either seed order.
  defp int_family_id(env),
    do: Inductive.builtin(env, :int) || int_family(Env.with_owner(env, "Std.Int")).name

  # `Std.Nat` excludes its own family while its source declaration is being
  # elaborated. Int is nevertheless seeded into that working environment, so
  # its constructors must use Nat's canonical identity even before the builtin
  # registry can contain the source-declared family. Baking the raw lookup here
  # produced `{:data, nil, ...}` in FromNat/NegativeSuccessor and poisoned every
  # transitive interface compiled through the Nat bootstrap.
  defp nat_family_id(env),
    do: Inductive.builtin(env, :nat) || nat_family(Env.with_owner(env, "Std.Nat")).name

  # struct_eq/struct_ne : Pi(a: Type0). Pi(_: a). Pi(_: a). Bool — under the
  # second binder the type param a is {:var, 0}; under the third it is {:var, 1}.
  # The type argument is computationally irrelevant (BEAM `==` is polymorphic and
  # emit drops it), so it is ERASED: a caller may pass its own erased type
  # parameter there without a relevance violation (#26). Erasure drops the type
  # argument, so the emitted spine is the two value operands.
  defp seed_struct_ops(env, bool_ty) do
    w = Grade.unrestricted()
    ty = {:pi, w, {:type, 0}, {:pi, w, {:var, 0}, {:pi, w, {:var, 1}, bool_ty}}}

    Enum.reduce(@struct_ops, env, fn {name, op_key}, acc ->
      acc
      |> Env.add_def(builtin_op_name(name), ty, nil, [:erased, :unrestricted, :unrestricted])
      |> Env.register_builtin_op(builtin_op_name(name), op_key)
    end)
  end

  defp seed_binops(env, ops, dom, bool_ty) do
    Enum.reduce(ops, env, fn {name, op_key}, acc ->
      cod = if op_key in @cmp_ops, do: bool_ty, else: dom
      ty = {:pi, Grade.unrestricted(), dom, {:pi, Grade.unrestricted(), dom, cod}}

      acc
      |> Env.add_def(builtin_op_name(name), ty, nil)
      |> Env.register_builtin_op(builtin_op_name(name), op_key)
    end)
  end

  defp seed_unops(env, ops, dom) do
    Enum.reduce(ops, env, fn {name, op_key}, acc ->
      ty = {:pi, Grade.unrestricted(), dom, dom}

      acc
      |> Env.add_def(builtin_op_name(name), ty, nil)
      |> Env.register_builtin_op(builtin_op_name(name), op_key)
    end)
  end

  defp builtin_op_name(name), do: Cure.Elab.Name.qualify("Std.Builtin", name)

  # A builtin whose bare family name is locally declared by the compiled module
  # is NOT seeded: the module's own declaration is the canonical family, and
  # pre-seeding a same-named family would leave the seed's constructors in
  # `ctor_to_family` (so a `match` on the local family reads as non-exhaustive).
  defp maybe_seed(env, key, family, ctors, exclude) do
    if MapSet.member?(exclude, family.name) or
         MapSet.member?(exclude, String.to_atom(Cure.Elab.Name.base(family.name))) do
      env
    else
      declare_and_register(env, key, family, ctors)
    end
  end

  defp seed_builtin(env, :bool, exclude),
    do:
      seed_builtin(
        env,
        :bool,
        bool_family(Env.with_owner(env, "Std.Bool")),
        bool_ctors(Env.with_owner(env, "Std.Bool")),
        exclude
      )

  defp seed_builtin(env, :any, exclude),
    do:
      seed_builtin(
        env,
        :any,
        any_family(Env.with_owner(env, "Std.Any")),
        [],
        exclude
      )

  defp seed_builtin(env, :nat, exclude),
    do:
      seed_builtin(
        env,
        :nat,
        nat_family(Env.with_owner(env, "Std.Nat")),
        nat_ctors(Env.with_owner(env, "Std.Nat")),
        exclude
      )

  defp seed_builtin(env, :int, exclude),
    do:
      seed_builtin(
        env,
        :int,
        int_family(Env.with_owner(env, "Std.Int")),
        int_ctors(Env.with_owner(env, "Std.Int")),
        exclude
      )

  defp seed_builtin(env, :eq, exclude),
    do:
      seed_builtin(
        env,
        :eq,
        eq_family(Env.with_owner(env, "Std.Equivalent")),
        eq_ctors(Env.with_owner(env, "Std.Equivalent")),
        exclude
      )

  defp seed_builtin(env, :sigma, exclude),
    do:
      seed_builtin(
        env,
        :sigma,
        sigma_family(Env.with_owner(env, "Std.Sigma")),
        sigma_ctors(Env.with_owner(env, "Std.Sigma")),
        exclude
      )

  defp seed_builtin(env, :list, exclude),
    do:
      seed_builtin(
        env,
        :list,
        list_family(Env.with_owner(env, "Std.List")),
        list_ctors(Env.with_owner(env, "Std.List")),
        exclude
      )

  defp seed_builtin(env, key, family, ctors, exclude), do: maybe_seed(env, key, family, ctors, exclude)

  defp declare_and_register(env, key, family, ctors) do
    fid = family.name
    env = Inductive.declare(env, family, ctors)
    :ok = validate!(env, key, fid)
    Inductive.register_builtin(env, key, fid)
  end

  # `Any` is an opaque top type: every value can be checked at it through the
  # kernel's subtyping rule, but it has no eliminator and therefore cannot be
  # abused as an empty inductive after widening.
  defp any_family(env), do: Inductive.opaque_family(Env.owned_name(env, :Any), [], 0)

  # Bool : Type0 = False | True  (both nullary)
  defp bool_family(env), do: Inductive.family(Env.owned_name(env, :Bool), [], [], 0)

  defp bool_ctors(env),
    do: [
      Inductive.ctor(Env.owned_name(env, :False), [], []),
      Inductive.ctor(Env.owned_name(env, :True), [], [])
    ]

  # Nat : Type0 = Z | S(Nat)  (S's field references the Nat family)
  defp nat_family(env), do: Inductive.family(Env.owned_name(env, :Nat), [], [], 0)

  defp nat_ctors(env),
    do: [
      Inductive.ctor(Env.owned_name(env, :Z), [], []),
      Inductive.ctor(Env.owned_name(env, :S), [{:_a0, {:data, Env.owned_name(env, :Nat), [], []}}], [])
    ]

  # Int : Type0 = FromNat(Nat) | NegativeSuccessor(Nat). Both fields reference the
  # Nat family (like S's field references Nat). Source of truth is the
  # @builtin(:int) decl in Std.Int (lib/std/int.cure); this seed is its
  # byte-for-byte mirror, pinned by the conformance drift harness.
  defp int_family(env), do: Inductive.family(Env.owned_name(env, :Int), [], [], 0)

  # FromNat / NegativeSuccessor belong to Std.Int (so the ctor NAMES are owned by
  # this env), but their single field is a *canonical* Nat — it must point at the
  # Std.Nat#Nat family, NOT a Std.Int-owned twin, or constructing FromNat(n) fails
  # to unify n's Nat against the prelude Nat. Nat is seeded before Int, so the
  # builtin lookup resolves here.
  defp int_ctors(env) do
    nat = {:data, nat_family_id(env), [], []}

    [
      Inductive.ctor(Env.owned_name(env, :FromNat), [{:_a0, nat}], []),
      Inductive.ctor(Env.owned_name(env, :NegativeSuccessor), [{:_a0, nat}], [])
    ]
  end

  # Equivalent : (a : Type) -> a -> a -> Type   (1 param `a`, 2 indices `x y : a`)
  #   reflexive : {w : a} -> Equivalent(a, w, w)  (single ctor, witness `w` erased)
  #
  # The genuine inductive identity type (spec 2026-07-04), retiring the primitive
  # `{:eq}`/`{:refl}`/`{:rewrite}` Core forms. The user-facing source of truth is
  # the `@builtin(:eq)` declaration in `Std.Equivalent` (lib/std/equivalent.cure);
  # this programmatic seed is its byte-for-byte mirror and the two are pinned equal
  # by the conformance harness. `w` is erased (quantity 0) so it is forced by index
  # unification when matching `reflexive` and dropped at runtime, while the surface
  # still supplies it explicitly at construction (`reflexive(x)`). K/UIP is
  # inherited from the existing index unifier — operator-signed-off 2026-07-04.
  defp eq_family(env),
    do: Inductive.family(Env.owned_name(env, :Equivalent), [a: {:type, 0}], [x: {:var, 0}, y: {:var, 1}], 0)

  defp eq_ctors(env),
    do: [
      Inductive.ctor(Env.owned_name(env, :reflexive), [w: {:var, 0}], [{:var, 0}, {:var, 0}], [:erased], [{:var, 1}])
    ]

  # Sigma : (a : Type) -> (b : (a) -> Type) -> Type   (2 params, no indices)
  #   mk_pair : (x : a) -> b(x) -> Sigma(a, b)
  # The library dependent pair (spec 2026-07-09-sigma-retirement), replacing the
  # primitive {:sigma}/{:pair}/{:fst}/{:snd} Core forms. Level-0 like Equivalent.
  # Source of truth is the @builtin(:sigma) decl in Std.Sigma; this seed is its
  # byte-for-byte mirror, pinned by the conformance drift test.
  defp sigma_family(env),
    do:
      Inductive.family(
        Env.owned_name(env, :Sigma),
        [a: {:type, 0}, b: {:pi, Grade.unrestricted(), {:var, 0}, {:type, 0}}],
        [],
        0
      )

  defp sigma_ctors(env),
    do: [
      Inductive.ctor(
        Env.owned_name(env, :mk_pair),
        # Second field `b(x)` is anonymous in the surface ctor sig, so the
        # elaborator auto-names it `_a1` (positional; the drift test pins this).
        [x: {:var, 1}, _a1: {:app, {:var, 1}, {:var, 0}}],
        [],
        [:unrestricted, :unrestricted],
        [{:var, 3}, {:var, 2}]
      )
    ]

  # List : (a : Type) -> Type   (1 param, no indices)
  #   Nil  : List(a)
  #   Cons : (x : a) -> (xs : List(a)) -> List(a)
  # First parametrized + self-referential builtin family (Cons's second field
  # references List itself, like nat's S). Source of truth is the @builtin(:list)
  # decl in Std.List; this seed is its byte-for-byte mirror, pinned by
  # builtin_list_drift_test.exs.
  defp list_family(env), do: Inductive.family(Env.owned_name(env, :List), [a: {:type, 0}], [], 0)

  # Field names auto-generated positionally by the elaborator (`_a0`/`_a1`); the
  # result-param term is the family's own param `a` reindexed under the ctor's
  # field binders (Nil: {:var, 0}; Cons: {:var, 2} beneath its two fields). The
  # drift test pins both spellings against the source declaration.
  defp list_ctors(env),
    do: [
      Inductive.ctor(Env.owned_name(env, :Nil), [], [], [], [{:var, 0}]),
      Inductive.ctor(
        Env.owned_name(env, :Cons),
        [_a0: {:var, 0}, _a1: {:data, Env.owned_name(env, :List), [{:var, 1}], []}],
        [],
        [:unrestricted, :unrestricted],
        [{:var, 2}]
      )
    ]
end
