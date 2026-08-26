defmodule Cure.Elab.DependentEliminatorTest do
  @moduledoc """
  Spec 2026-07-08-neutral-app-sort (Sigma D1): motives applying a type-family
  head — `b(first(p))` — sort via reify+infer (kernel.ex napp clause); an
  adversarial motive applying a non-function head rejects cleanly (:bad_motive).
  Surface probes drive Program.elaborate. (The former §2.4 bare-`{:pair,…}` crash
  probe retired with primitive Sigma in D2 — see the note in the describe block.)
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Kernel}
  alias Cure.Elab.Program

  @probe """
  mod P
    type Nat = Z | S(Nat)
    type MySigma(a: Type, b: (a) -> Type) indices ()
      mk_pair : (x: a) -> b(x) -> MySigma(a, b)
    fn first({a: Type}, {b: (a) -> Type}, p: MySigma(a, b)) -> a = match p
      mk_pair(x, y) -> x
    fn second({a: Type}, {b: (a) -> Type}, p: MySigma(a, b)) -> b(first(p)) = match p
      mk_pair(x, y) -> y
    fn const_nat(x: Nat) -> Type = Nat
    fn mk() -> MySigma(Nat, const_nat) = mk_pair(Z(), S(Z()))
    fn run_second() -> Nat = second(mk())
  end
  """

  # RED THROUGH TASK 1 (expected — spec §7.1): the implicit-param probe needs
  # Task 1b's type-position implicit insertion; kernel-only it still rejects
  # :bad_motive on the under-applied motive. Goes green at Task 1b Step 4.
  test "D1 probe: dependent second projection elaborates (b(first(p)) motive)" do
    assert {:ok, _env} = Program.elaborate(@probe)
  end

  # Kernel-enabler pin (green at Task 1 Step 6, BEFORE Task 1b): the identical
  # probe with EXPLICIT type params lowers `b(first(a, b, p))` to a full spine,
  # so it isolates the napp kernel clause from the Task 1b elaborator fix —
  # executor-verified accepted with the two clauses alone (spec §7.1).
  @explicit_probe """
  mod P
    type Nat = Z | S(Nat)
    type MySigma(a: Type, b: (a) -> Type) indices ()
      mk_pair : (x: a) -> b(x) -> MySigma(a, b)
    fn first(a: Type, b: (a) -> Type, p: MySigma(a, b)) -> a = match p
      mk_pair(x, y) -> x
    fn second(a: Type, b: (a) -> Type, p: MySigma(a, b)) -> b(first(a, b, p)) = match p
      mk_pair(x, y) -> y
  end
  """

  test "kernel-enabler pin: explicit-param dependent second projection elaborates" do
    assert {:ok, _env} = Program.elaborate(@explicit_probe)
  end

  test "D1 probe: second(mk_pair(x, y)) reduces/runs correctly on BEAM (spec §4 item 2)" do
    # Monomorphic instance: a := Nat, b := const_nat (a named type-level def),
    # x = Z(), y = S(Z()). LATITUDE USED (plan Task 1's wrapper-adjustment
    # clause): the original wrapper `second(mk_pair(Z(), S(Z())))` required
    # solving `?b(Z()) =?= Nat` — NOT a Miller pattern (the meta's argument is a
    # closed ctor, not a bound var; dep07's `the2` solves `?F(n)` under a
    # binder, a genuinely different shape) — so `b` is pinned by checking the
    # pair against `MySigma(Nat, const_nat)` instead; `second(mk())` still runs
    # on a genuine mk_pair instance and the asserted runtime value is unchanged.
    # Also pins the `first(mk_pair(x,y)) -> x` ι-reduction (via const_nat/first
    # δ-reduction in `run_second`'s return-type check) per spec §4 item 2.
    {:ok, env} = Program.elaborate(@probe)
    # `functions:` must list every def actually called, not just the entry point —
    # `run_second` calls `second` and `mk`; `second` calls `first` — confirmed
    # against `test/cure/elab/first_class_function_test.exs`'s multi-name
    # `functions:` lists (e.g. `[:ap, :inc, :g]`); `module_forms/3`
    # (emit.ex:80-89) emits forms only for the exact names given, no
    # transitive-callee closure. `const_nat` is type-level only (erased at
    # runtime), so it is not emitted.
    {:ok, mod} =
      Cure.Elab.Emit.compile_and_load(env,
        module: :"Cure.DependentEliminatorProbe",
        functions: [:run_second, :second, :first, :mk]
      )

    # Runtime ctor encoding verified against test/cure/elab/auto_generalize_test.exs
    # and conditional_test.exs: nullary ctors compile to bare atoms (Z -> :Z),
    # ctors with args to tagged tuples (S(Z()) -> {:S, :Z}).
    assert apply(mod, :run_second, []) == {:S, :Z}
  end

  test "negative: non-type-valued head in type position still rejects" do
    src = """
    mod P
      type Nat = Z | S(Nat)
      type MySigma(a: Type, b: (a) -> Type) indices ()
        mk_pair : (x: a) -> b(x) -> MySigma(a, b)
      fn bad({a: Type}, {b: (a) -> Type}, {g: (a) -> Nat}, p: MySigma(a, b)) -> g(first(p)) = match p
        mk_pair(x, y) -> y
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end

  test "negative: ill-typed argument to the type-family head still rejects" do
    src = """
    mod P
      type Nat = Z | S(Nat)
      type Other = Mk
      type MySigma(a: Type, b: (a) -> Type) indices ()
        mk_pair : (x: a) -> b(x) -> MySigma(a, b)
      fn bad({b: (Other) -> Type}, p: MySigma(Nat, ?)) -> b(Z()) = Z()
    end
    """

    # The exact surface framing may need adjustment (see latitude note); the
    # requirement is: a type-position application whose argument does not match
    # the head's domain is rejected, not accepted.
    assert {:error, _} = Program.elaborate(src)
  end

  # §2.4 crash probe: hand-built Core, driven straight at Kernel.infer. The
  # non-function variant applies the motive's own Nat-typed binder (dies at
  # ensure_pi). The PAIR variant MUST use a FUNCTION-typed head (spec §7.6,
  # executor-verified): only then does infer get past ensure_pi and reach the
  # pair argument — check against the non-Σ domain falls through to infer on a
  # bare {:pair,…}, the exact §2.4 crash site. A Nat-typed head applied to a
  # pair never reaches the pair and proves nothing about the defensive clause.
  describe "§2.4 adversarial motives reject cleanly (never crash)" do
    defp nat_env do
      {:ok, env} = Program.elaborate("mod P\n  type Nat = Z | S(Nat)\nend\n")
      env
    end

    defp bad_motive_case(motive) do
      {:case, {:ctor, :Z, []}, motive, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :Z, []}}]}
    end

    test "motive applying a non-function head rejects :bad_motive" do
      ctx = Context.empty(nat_env())
      nat = {:data, :Nat, [], []}
      motive = {:lam, Cure.Core.Grade.unrestricted(), nat, {:app, {:var, 0}, {:ctor, :Z, []}}}
      assert {:error, :bad_motive} = Kernel.infer(ctx, bad_motive_case(motive))
    end

    # NOTE (D2): the former "function-typed head applied to a bare `{:pair,…}`"
    # probe pinned the defensive `infer(_ctx, {:pair,_,_})` clause
    # (kernel.ex:125-128). Primitive Sigma is retired: `{:pair,…}` is no longer a
    # Core node, so the adversarial term is inexpressible — a strictly stronger
    # guarantee than the clean `:bad_motive` rejection that probe asserted. The
    # probe was removed together with the clause it pinned (spec §1.3).
  end
end
