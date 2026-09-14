defmodule Cure.Elab.BindPipeTest do
  @moduledoc """
  End-to-end coverage for the binder pipe `|x|>` (docs/BIND_PIPE.md).

  `a |x|> f(x)` desugars to `and_then(a, fn(x) -> f(x))` (§7.2), resolved by the
  ordinary interface coherence against the `Monad(m)` instance for the chain's
  monad `m` (`Std.Monad`). The final stage auto-lifts with `pure` when it is a
  pure value (§5.4). The whole chain short-circuits on the failure arm (§6.2).

  These tests drive the full pipeline — elaborate, emit, load, run — so they
  assert the runtime behaviour the spec's Appendix A pins, not just the AST.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Program, Emit}

  defp eval(src, fname, mod) do
    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [fname])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, fname, [])
  end

  describe "Result monad (§A.1, §A.2, §A.4)" do
    test "selection and short-circuit on the Ok arm" do
      src = """
      mod BP1
        use Std.Monad
        use Std.Result
        fn go() -> Result(Int, Atom) = ok(1) |x|> ok(x + 1) |y|> ok(y * 2)
      end
      """

      assert eval(src, :go, :"Cure.BP1") == {:ok, 4}
    end

    test "short-circuits on Error without evaluating later stages" do
      src = """
      mod BP2
        use Std.Monad
        use Std.Result
        fn go() -> Result(Int, Atom) = error(:e) |x|> ok(x + 1) |y|> ok(y * 2)
      end
      """

      assert eval(src, :go, :"Cure.BP2") == {:error, :e}
    end

    test "a mid-chain error short-circuits" do
      src = """
      mod BP3
        use Std.Monad
        use Std.Result
        fn go() -> Result(Int, Atom) = ok(1) |x|> error(:mid) |y|> ok(y)
      end
      """

      assert eval(src, :go, :"Cure.BP3") == {:error, :mid}
    end

    test "final-stage auto-lift: a pure final value is lifted with `pure`" do
      src = """
      mod BP4
        use Std.Monad
        use Std.Result
        fn go() -> Result(Int, Atom) = ok(1) |x|> x + 1
      end
      """

      assert eval(src, :go, :"Cure.BP4") == {:ok, 2}
    end

    test "an already-monadic final stage is used as-is" do
      src = """
      mod BP5
        use Std.Monad
        use Std.Result
        fn go() -> Result(Int, Atom) = ok(1) |x|> ok(x + 1)
      end
      """

      assert eval(src, :go, :"Cure.BP5") == {:ok, 2}
    end

    test "scoping: an earlier binder is visible in a later stage and the final" do
      src = """
      mod BP6
        use Std.Monad
        use Std.Result
        fn go() -> Result(Int, Atom) = ok(1) |x|> ok(x + 1) |y|> ok(x + y)
      end
      """

      assert eval(src, :go, :"Cure.BP6") == {:ok, 3}
    end
  end

  describe "Option monad (§A.3)" do
    test "Some chains and short-circuits on None" do
      src = """
      mod BP7
        use Std.Monad
        use Std.Option
        fn go() -> Option(Int) = Some(3) |x|> Some(x * 2) |y|> Some(y + 1)
      end
      """

      assert eval(src, :go, :"Cure.BP7") == {:some, 7}
    end

    test "None short-circuits" do
      src = """
      mod BP8
        use Std.Monad
        use Std.Option
        fn go() -> Option(Int) = None() |x|> Some(x * 2)
      end
      """

      assert eval(src, :go, :"Cure.BP8") == :none
    end
  end

  describe "equivalence with `do` (§7.3, §A.6)" do
    test "a binder pipe and the equivalent `do` block agree" do
      pipe = """
      mod BP9
        use Std.Monad
        use Std.Result
        fn go() -> Result(Int, Atom) = ok(1) |x|> ok(x + 1)
      end
      """

      do_block = """
      mod BP9
        use Std.Monad
        use Std.Result
        fn go() -> Result(Int, Atom) =
          do
            x <- ok(1)
            ok(x + 1)
      end
      """

      assert eval(pipe, :go, :"Cure.BP9a") == eval(do_block, :go, :"Cure.BP9b")
    end
  end

  describe "the motivating ledger example (§1, §10.1)" do
    test "a three-stage Result chain runs and short-circuits" do
      src = """
      mod Ledger
        use Std.Monad
        use Std.Result
        rec Account
          balance: Int
          held: Int

        fn find_account(id: Int) -> Result(Account, String) =
          pickup
            id == 1 -> Ok(Account{balance: 100, held: 0})
            else    -> Error("no account")

        fn subtract(balance: Int, amount: Int) -> Result(Int, String) =
          pickup
            balance >= amount -> Ok(balance - amount)
            else              -> Error("insufficient")

        fn add(a: Int, b: Int) -> Int = a + b

        fn reserve(id: Int, amount: Int) -> Result(Int, String) =
          find_account(id)
          |account|> subtract(account.balance, amount)
          |new_balance|> add(account.held, new_balance)
      end
      """

      {:ok, env} = Program.elaborate(src)
      fns = Program.reachable_def_names(env, [:reserve])
      {:ok, m} = Emit.compile_and_load(env, module: :"Cure.Ledger", functions: fns)

      # Success path: 100 - 30 = 70, 0 + 70 = 70.
      assert apply(m, :reserve, [1, 30]) == {:ok, 70}
      # Failure path: insufficient balance short-circuits. `String` is nominal
      # (docs/BIND_PIPE.md era stdlib) and runs to the tagged `{:String, charlist}`
      # pair (see `Cure.Elab.StringLiteralTest`), not a plain Elixir string.
      assert apply(m, :reserve, [1, 999]) == {:error, {:String, ~c"insufficient"}}
      # Failure path: unknown account short-circuits the whole chain.
      assert apply(m, :reserve, [2, 30]) == {:error, {:String, ~c"no account"}}
    end
  end

  describe "static rejection (§A.5)" do
    test "no `Monad` instance in scope is a clean error" do
      # `Int` has no `Monad` instance, so the chain cannot resolve a bind.
      src = """
      mod BP10
        fn go() -> Int = 1 |x|> x + 1
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end
  end
end
