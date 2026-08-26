defmodule Cure.Elab.FloatDivisionRuntimeTest do
  @moduledoc """
  Regression: Cure's `/` is type-directed (Int/Int is integer division, Float/Float
  is float division), and the two BEAM instructions are NOT interchangeable —
  `erlang:div/2` raises badarith on floats, and `erlang:'/'/2` returns a float for
  two ints.

  `Builtins` registered `int_div` and `float_div` under the SAME op key `:div`, and
  `Emit.erl_binop/1` lowered `:div` to Erlang's integer `div`. So `a / b` on Float
  variables crashed at runtime — while `Eval.fold(:div, [{:vfloat,_},{:vfloat,_}])`
  computed the correct quotient. The normaliser and the emitter disagreed about the
  same term.

  `float_prim_test.exs` did not catch this: it drives the kernel's compile-time
  normaliser over LITERAL operands, which constant-folds through `Eval.fold` and
  never reaches emitted code. These tests use VARIABLE operands specifically so the
  division survives to the BEAM.

  `add`/`sub`/`mul` and the comparisons may safely share an op key with their int
  twins, because `+ - * < =< > >= == /=` are int/float polymorphic on the BEAM.
  Division is the sole operator where they are different instructions. If you add
  another such operator, give it its own op key too.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Builtins, Env}
  alias Cure.Elab.{Emit, Program}

  describe "dependent pipeline (Emit)" do
    test "float division on variable operands computes the quotient" do
      src = """
      mod M
        fn favg(a: Float, b: Float) -> Float = a / b
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      assert {:ok, mod} =
               Emit.compile_and_load(env,
                 module: :"Cure.Test.FloatDivDependent",
                 functions: [:favg]
               )

      assert apply(mod, :favg, [7.0, 2.0]) == 3.5
    end

    test "int division on variable operands still truncates (not float `/`)" do
      src = """
      mod M
        fn idiv(a: Int, b: Int) -> Int = a / b
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      assert {:ok, mod} =
               Emit.compile_and_load(env,
                 module: :"Cure.Test.IntDivDependent",
                 functions: [:idiv]
               )

      assert apply(mod, :idiv, [7, 2]) == 3
    end

    test "float_div and int_div carry distinct op keys" do
      env = Builtins.seed(Env.empty())
      assert Env.builtin_op(env, :int_div) == :div
      assert Env.builtin_op(env, :float_div) == :fdiv
    end
  end

  describe "runtime division (end-to-end through the sole pipeline)" do
    # `/` dispatches at runtime on is_float/1. Both operands are bound once, so
    # neither is evaluated twice — these outcomes are pipeline-independent.
    test "float division on variable operands computes the quotient" do
      assert eval!(
               """
               mod ClassicFloatDiv
                 fn favg(a: Float, b: Float) -> Float = a / b
               end
               """,
               :favg,
               [7.0, 2.0]
             ) == 3.5
    end

    test "int division on variable operands still truncates" do
      assert eval!(
               """
               mod ClassicIntDiv
                 fn idiv(a: Int, b: Int) -> Int = a / b
               end
               """,
               :idiv,
               [7, 2]
             ) == 3
    end

    test "a divisor expression is evaluated exactly once" do
      # The runtime dispatch binds both operands before testing is_float/1. If it
      # instead inlined the operand into both the guard and the arms, a side-effecting
      # divisor would run twice.
      assert eval!(
               """
               mod ClassicDivOnce
                 fn f(a: Int) -> Int = a / (a - 5)
               end
               """,
               :f,
               [11]
             ) == 1
    end
  end

  defp eval!(source, fun, args) do
    {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    apply(module, fun, args)
  end
end
