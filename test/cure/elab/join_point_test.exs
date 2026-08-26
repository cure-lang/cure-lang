defmodule Cure.Elab.JoinPointTest do
  @moduledoc """
  Slice 4c (QTT plan): a `match`'s catch-all body is bound **once**, not copied
  into every uncovered constructor's branch.

  Core `:case` has no default branch, so a surface `_ -> e` / `x -> e` arm must
  become one Core branch per *uncovered* constructor. `elaborate_default_branch/10`
  used to surface-substitute the catch-all variable and re-elaborate `e` from
  scratch for each one. The copies are **multiplicative** across nesting: `k`
  nested catch-alls over an `n`-constructor type produce `(n-1)^k` copies of the
  body. Measured before the fix: 5 copies for one catch-all over a 6-constructor
  type, and **25** for two nested ones. On an ESP32 that is paid in flash.

  The fix is a join point, spelled with Core formers that already exist. The
  `:case` is wrapped in the `:let` binder, which binds

      j = {:lam, ω, S, e}   at type   {:pi, ω, S, R}

  — literally the motive λ with `:lam` rewritten to `:pi` — and each defaulted
  branch becomes `{:app, j, scrut}`. The λ is what supplies laziness: a bare
  `:let` of `e` would evaluate the catch-all body even when a real arm matches.
  Binding the scrutinee as the λ's argument is also exactly what a *named*
  catch-all `x -> g(x)` means, so the substitution disappears rather than moving.

  This is a term-size fix, not a soundness fix. Idris combines branch usages by
  agreement rather than summation (`LinearCheck.idr:528-540`), and every copy the
  expansion made landed in a *disjoint* constructor branch — so a linear variable
  in a copied body was always counted once. See the plan's "Known prerequisite".

  Scope, and therefore the negative tests below: the join point fires only when
  the motive is non-dependent and **≥2** constructors are uncovered. One
  uncovered constructor would pay a closure to save nothing.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}
  alias Cure.Core.{Env, Validator}

  defp body(env, name), do: env |> Env.get_def(name) |> Map.fetch!(:body)

  defp count(env, name, pred),
    do: env |> body(name) |> Validator.nodes() |> Enum.count(pred)

  defp calls(env, name, callee) do
    key = Env.resolve_key(env, env.defs, callee)
    count(env, name, &(&1 == {:global, key}))
  end

  defp lets(env, name), do: count(env, name, &match?({:let, _, _, _, _}, &1))

  # Six constructors, one arm covered: the catch-all must reach B, D, E, G, H.
  @six """
  mod JPSix
    type C = A | B | D | E | G | H
    fn kont(a: Int) -> Int = a
    fn hit(a: Int) -> Int = a
    fn f(x: C, n: Int) -> Int =
      match x
        A() -> hit(n)
        _ -> kont(n)
  end
  """

  # Two nested catch-alls. Pre-fix this elaborated 25 copies of `kont`.
  @nested """
  mod JPNested
    type C = A | B | D | E | G | H
    fn kont(a: Int) -> Int = a
    fn hit(a: Int) -> Int = a
    fn f(x: C, y: C, n: Int) -> Int =
      match x
        A() -> hit(n)
        _ -> match y
          A() -> hit(n)
          _ -> kont(n)
  end
  """

  describe "the catch-all body is elaborated once" do
    test "one catch-all over a 6-constructor type emits ONE copy, not 5" do
      {:ok, env} = Program.elaborate(@six)
      assert calls(env, :f, :kont) == 1
    end

    test "the join point is a let-bound lambda" do
      {:ok, env} = Program.elaborate(@six)
      assert lets(env, :f) == 1
    end

    test "two nested catch-alls emit ONE copy, not 25 — sharing composes" do
      # The outer join binds the inner `match y` once; the inner join binds
      # `kont(n)` once inside it. Nesting therefore adds a binding rather than
      # multiplying copies. `hit` legitimately appears twice — those are two
      # distinct matched arms, not copies of one body.
      {:ok, env} = Program.elaborate(@nested)
      assert calls(env, :f, :kont) == 1
      assert calls(env, :f, :hit) == 2
    end
  end

  describe "semantics are preserved" do
    test "every constructor still computes what it did before" do
      src = """
      mod JPSem
        type C = A | B | D | E | G | H
        fn f(x: C, n: Int) -> Int =
          match x
            A() -> n
            _ -> 0
        fn t_a() -> Int = f(A(), 7)
        fn t_b() -> Int = f(B(), 7)
        fn t_h() -> Int = f(H(), 7)
      end
      """

      {:ok, env} = Program.elaborate(src)

      {:ok, mod} =
        Emit.compile_and_load(env, module: :"Cure.JPSem", functions: [:f, :t_a, :t_b, :t_h])

      assert mod.t_a() == 7, "the matched arm must still win"
      assert mod.t_b() == 0, "the first defaulted constructor must reach the catch-all"
      assert mod.t_h() == 0, "so must the last one"
    end

    test "a NAMED catch-all still sees the scrutinee's value" do
      # `y` is now the join lambda's binder rather than a substituted
      # reconstruction `C($C_1…)`. It must still be the value that was scrutinised.
      src = """
      mod JPNamed
        type C = A | B | D
        fn rank(y: C) -> Int =
          match y
            A() -> 10
            B() -> 20
            D() -> 30
        fn f(x: C) -> Int =
          match x
            A() -> 1
            y -> rank(y)
        fn t_b() -> Int = f(B())
        fn t_d() -> Int = f(D())
      end
      """

      {:ok, env} = Program.elaborate(src)
      assert calls(env, :f, :rank) == 1

      {:ok, mod} =
        Emit.compile_and_load(env, module: :"Cure.JPNamed", functions: [:rank, :f, :t_b, :t_d])

      assert mod.t_b() == 20
      assert mod.t_d() == 30
    end

    test "the catch-all does NOT run when a real arm matches" do
      # A bare `:let` of the body (no λ) would be eager. `loop()` diverges, so an
      # eager join point turns `f(A())` into a hang instead of `1`.
      src = """
      mod JPLazy
        type C = A | B | D | E
        fn loop(n: Int) -> Int = loop(n)
        fn f(x: C) -> Int =
          match x
            A() -> 1
            _ -> loop(0)
        fn t_a() -> Int = f(A())
      end
      """

      {:ok, env} = Program.elaborate(src)

      {:ok, mod} =
        Emit.compile_and_load(env, module: :"Cure.JPLazy", functions: [:loop, :f, :t_a])

      task = Task.async(fn -> mod.t_a() end)
      assert Task.yield(task, 2_000) == {:ok, 1}, "the catch-all was evaluated eagerly"
      Task.shutdown(task, :brutal_kill)
    end
  end

  describe "the join point does not fire where it would not pay" do
    test "a single uncovered constructor emits no join point" do
      src = """
      mod JPOne
        type Two = T | F
        fn f(x: Two) -> Int =
          match x
            T() -> 1
            _ -> 2
      end
      """

      {:ok, env} = Program.elaborate(src)
      assert lets(env, :f) == 0
    end

    test "an indexed family keeps today's expansion and still typechecks" do
      # A dependent motive would need each branch's reconstructed `C(args…)`,
      # including its erased telescope args, rather than the scrutinee. Out of
      # scope for 4c — it must be left exactly as it was.
      src = """
      mod JPVec
        type Nat = Z | S(Nat)
        type Vector(a: Type) indices (n: Nat)
          empty : Vector(a, Z)
          prepend : a -> Vector(a, n) -> Vector(a, S(n))
        fn is_empty(v: Vector(Nat, Z)) -> Int =
          match v
            empty() -> 1
            _ -> 0
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert lets(env, :is_empty) == 0
    end
  end
end
