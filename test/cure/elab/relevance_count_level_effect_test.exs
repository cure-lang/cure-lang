defmodule Cure.Elab.RelevanceCountLevelEffectTest do
  @moduledoc """
  `Relevance.count_level/3` — the occurrence counter that authorises the un-join — must
  descend into the Effect formers.

  `count_level` is the sole evidence for `join_binder_safe?/4`, which decides whether a
  `let`-bound continuation may be UN-JOINED. That optimisation is what lets `Relevance`
  count the continuation's captured variables ONCE (unscaled) instead of ω-scaling them the
  way a general closure demands — and it is sound only under the property `count_level` is
  supposed to establish: that the continuation runs at most once on any path.

  `count_level` enumerated `:lam`, `:pi`, `:let`, `:app`, `:ctor`, `:data` and `:case`, then
  fell to `count_level(_leaf, _depth, _t), do: 0`. `{:effect_bind, _, _}` and
  `{:effect_pure, _}` are not leaves — they carry arbitrary subterms — so every occurrence of
  the join binder inside an effect node was counted as ZERO. A branch that called the
  continuation any number of times was therefore certified as "does not mention it at all",
  the un-join fired, and those calls were never charged to anyone.

  The exploit below is that hole, minimised. `n` is `:affine` (at most one use). The
  continuation `k` consumes `n` exactly once. The `T` branch calls `k` TWICE — so on the `T`
  path `n` is consumed twice — but both calls sit inside the `effect_bind` that `let a = k(0)`
  lowers to, so `count_level` reported 0, the join was declared safe, and the program was
  ACCEPTED. Affine is where this bites: the un-join under-counts to zero, and zero is a legal
  affine usage, so the violation is not merely mis-reported — it is admitted.

  The pure twin is the control. It is the same program with the two calls in an ordinary
  `let`, a former `count_level` DOES descend into; it counts 2, refuses the un-join, falls back
  to the sound ω-scale of a general closure, and rejects. Nothing about the program's meaning
  differs — only whether the calls were hidden behind a former the counter had never been
  taught about. That contrast is the whole defect.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @effect_preamble """
  mod CA
    @extern(:erlang, :display, 1)
    fn lsink(@linear v : Int) -> Effect(Int)
    type Two = T | F
  """

  describe "a continuation called twice through effect nodes is charged for both calls" do
    test "calling the continuation twice on one path VIOLATES an affine capture" do
      # `n` is affine, `k` consumes it once, and the `T` path runs `k` twice.
      src =
        @effect_preamble <>
          """
            fn f(x: Two, @affine n : Int) -> Effect(Int) =
              let k : (Int) -> Effect(Int) = fn(y) -> lsink(n)
              match x
                T() ->
                  let a = k(0)
                  k(0)
                F() -> k(0)
          """

      assert {:error, {:usage_violation, %{declared: :affine, kind: :param}}} =
               Program.semantic_result(Program.elaborate(src))
    end

    test "the pure twin — same shape, calls NOT hidden in effect nodes — was always rejected" do
      # The control. `count_level` has a `:let` clause, so here it sees both calls, refuses the
      # un-join, and ω-scales the closure. Identical meaning; opposite verdict, before the fix.
      src = """
      mod CP
        fn psink(@linear v : Int) -> Int = v
        type Two = T | F
        fn h(x: Two, @affine n : Int) -> Int =
          let k : (Int) -> Int = fn(y) -> psink(n)
          match x
            T() ->
              let a = k(0)
              k(0)
            F() -> k(0)
      """

      assert {:error, {:usage_violation, %{declared: :affine, kind: :param}}} =
               Program.semantic_result(Program.elaborate(src))
    end

    test "a genuinely one-shot continuation still un-joins and is ACCEPTED" do
      # The un-join must be REPAIRED, not disabled. `k` runs at most once on either path, so
      # its capture of `n` costs one use, and the affine obligation is met. If this flips to a
      # rejection the fix has simply switched the optimisation off.
      src =
        @effect_preamble <>
          """
            fn g(x: Two, @affine n : Int) -> Effect(Int) =
              let k : (Int) -> Effect(Int) = fn(y) -> lsink(n)
              match x
                T() -> k(0)
                F() -> k(0)
          """

      assert {:ok, _env} = Program.semantic_result(Program.elaborate(src))
    end
  end
end
