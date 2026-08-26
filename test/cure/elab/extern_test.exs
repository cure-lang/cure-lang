defmodule Cure.Elab.ExternTest do
  @moduledoc """
  `@extern(:mod, :fn, arity)` FFI in the dependent pipeline (Wave 3). A bodyless
  extern is a typed opaque postulate: its declared Π is asserted (an FFI axiom,
  not kernel-proven — see spec §4 Claim B), it stays an opaque neutral in the
  kernel, and emit lowers it to a direct Erlang remote call. Kernel untouched.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit, TotalityClosure}
  alias Cure.Core.Env

  test "a bodyless @extern declaration elaborates" do
    src = "mod M\n  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\nend\n"
    assert {:ok, _env} = Program.elaborate(src)
  end

  test "the elaborated extern retains its declared arrow type (signature not discarded)" do
    src = "mod M\n  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\nend\n"
    {:ok, env} = Program.elaborate(src)
    # The behavioral contract: a def named `length` exists with a Pi type whose
    # codomain is Int. Pin at least that the def is present and not {:hole,_}.
    def_entry = extern_def!(env, :length)
    refute match?({:hole, _}, Map.get(def_entry, :body))
    assert Map.get(def_entry, :type) != nil
  end

  test "TotalityClosure does not certify an extern reached from a type-level index" do
    # `extdec`'s call appears in constructor `mk`'s result index (mirroring the
    # `andd(d1, d2)`-in-result-index precedent in indexed_declarations_test.exs),
    # so seed_globals pulls it into the type-level closure. It is an extern with
    # no Core body to certify — certify_type_level must skip it, never hand its
    # sentinel to Kernel.check.
    src =
      "mod M\n" <>
        "  type Dec = Dcoupled | Causal\n" <>
        "  @extern(:erlang, :abs, 1)\n  fn extdec(x: Dec) -> Dec\n" <>
        "  type Boxed indices (d: Dec)\n" <>
        "    mk : Boxed(extdec(Causal))\n" <>
        "end\n"

    {:ok, env} = Program.elaborate(src)

    # Reachability (falsifiability): :extdec must actually be in the closure,
    # or this test would pass vacuously.
    assert MapSet.member?(TotalityClosure.type_level_fns(env), :"M#extdec")

    # The mechanism: certify_type_level must succeed (not
    # {:error, {:totality_required, :extdec}}), because an extern is skipped.
    assert {:ok, _} = TotalityClosure.certify_type_level(env)
  end

  test "an @extern typechecks AND ships — issues the real remote call" do
    src = "mod M\n  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\nend\n"
    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Extern1", functions: [:length])
    assert apply(mod, :length, [[1, 2, 3]]) == 3
  end

  test "a 0-arity and a 2-arity extern both wire params correctly" do
    src =
      "mod M\n" <>
        "  @extern(:erlang, :max, 2)\n  fn imax(a: Int, b: Int) -> Int\n" <>
        "end\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Extern2", functions: [:imax])
    assert apply(mod, :imax, [3, 7]) == 7

    src0 = "mod M\n  @extern(:erlang, :time, 0)\n  fn now() -> Int\nend\n"
    {:ok, env0} = Program.elaborate(src0)
    {:ok, mod0} = Emit.compile_and_load(env0, module: :"Cure.Extern0", functions: [:now])
    # :erlang.time/0 returns a {H,M,S} tuple; just assert it runs and returns a value.
    assert apply(mod0, :now, []) != nil
  end

  test "an extern mixed with a normal dependent function — whole module elaborates + emits" do
    src =
      "mod M\n" <>
        "  @extern(:erlang, :length, 1)\n  fn length(xs: List(Int)) -> Int\n" <>
        "  fn double(n: Int) -> Int = n + n\n" <>
        "end\n"

    {:ok, env} = Program.elaborate(src)
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.Extern3", functions: [:length, :double])
    assert apply(mod, :length, [[1, 2]]) == 2
    assert apply(mod, :double, [21]) == 42
  end

  describe "the @extern arity is the target's arity, i.e. the def's PRESENT arity" do
    # `extern_form/3` used to build the emitted function's BEAM arity, and the number of
    # arguments it passed to the remote call, from the raw integer literal — never from the
    # def's own `:unrestricted` quantities, the way `real_function_form/3` and every CALL SITE
    # (`present_arity/2`) do. Nothing cross-checked the two, so they were free to diverge.
    #
    # An extern with an erased implicit has a present arity strictly below its surface
    # telescope length. Auto-generalization inserts one for any free lowercase type var even
    # when the user writes none, so this is not an exotic shape. A user counting the parens
    # writes 2 for `head({T: Type}, xs: List(T))`; `Emit` then generated `head/2` calling
    # `erlang:hd(V0, V1)`, while every Cure caller invoked `head/1`. Both forms compiled; the
    # module broke the moment anything called it.

    test "an extern with an erased implicit param emits at its present arity and calls correctly" do
      src = """
      mod M
        @extern(:erlang, :hd, 1)
        fn head({T: Type}, xs: List(T)) -> T
        fn use_head(xs: List(Int)) -> Int = head(xs)
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      assert {:ok, mod} =
               Emit.compile_and_load(env,
                 module: :"Cure.ExternErasedArity",
                 functions: [:head, :use_head]
               )

      assert {:head, 1} in mod.module_info(:exports)
      assert apply(mod, :use_head, [[1, 2, 3]]) == 1
    end

    test "a literal arity that disagrees with the present arity is rejected" do
      src = """
      mod M
        @extern(:erlang, :hd, 2)
        fn head({T: Type}, xs: List(T)) -> T
      end
      """

      assert {:error, {:extern_arity_mismatch, %{name: :head, declared: 2, present: 1, span: span}}} =
               Program.elaborate(src)

      assert {span.start_line, span.start_column, span.end_column} == {2, 25, 26}
    end

    test "a nullary extern still means arity 0" do
      src = "mod M\n  @extern(:erlang, :time, 0)\n  fn now() -> Int\nend\n"
      assert {:ok, _env} = Program.elaborate(src)
    end
  end

  defp extern_def!(env, name), do: Env.get_def(env, name) || flunk("no def #{name}")
end
