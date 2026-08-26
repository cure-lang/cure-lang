defmodule Cure.Elab.NamedArgumentsTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler
  alias Cure.Core.Env
  alias Cure.Elab.{Erase, Program}

  defp compile!(source) do
    {:ok, module} = Compiler.compile_and_load(source, emit_events: false)
    module
  end

  defp error!(source) do
    assert {:error, error} = Compiler.compile_and_load(source, emit_events: false)
    unwrap(error)
  end

  defp unwrap({:source_context, reason, _context}), do: unwrap(reason)
  defp unwrap({:codegen_error, reason}), do: unwrap(reason)
  defp unwrap({:type_error, [reason | _]}), do: unwrap(reason)
  defp unwrap({:error, reason}), do: unwrap(reason)
  defp unwrap(reason), do: reason

  test "named arguments reorder into declaration order before runtime lowering" do
    module =
      compile!("""
      mod NamedReorder
        fn digits(a: Int, b: Int, c: Int) -> Int = a * 100 + b * 10 + c
        fn go() -> Int = digits(c: 3, a: 1, b: 2)
      end
      """)

    assert apply(module, :go, []) == 123
  end

  test "labels disappear before Core and erasure" do
    {:ok, env} =
      Program.elaborate("""
      mod NamedCore
        fn digits(a: Int, b: Int, c: Int) -> Int = a * 100 + b * 10 + c
        fn positional() -> Int = digits(1, 2, 3)
        fn named() -> Int = digits(c: 3, a: 1, b: 2)
      end
      """)

    positional = Env.get_def(env, :"NamedCore#positional").body
    named = Env.get_def(env, :"NamedCore#named").body
    assert positional == named
    assert Erase.erase(env, positional) == Erase.erase(env, named)
  end

  test "positional prefix fills leftmost parameters and following names may reorder" do
    module =
      compile!("""
      mod NamedMixed
        fn digits(a: Int, b: Int, c: Int) -> Int = a * 100 + b * 10 + c
        fn go() -> Int = digits(1, c: 3, b: 2)
      end
      """)

    assert apply(module, :go, []) == 123
  end

  test "pipe insertion remains the positional prefix before reordered names" do
    module =
      compile!("""
      mod NamedPipe
        fn digits(a: Int, b: Int, c: Int) -> Int = a * 100 + b * 10 + c
        fn go() -> Int = 1 |> digits(c: 3, b: 2)
      end
      """)

    assert apply(module, :go, []) == 123
  end

  test "a positional argument after a named argument is E115-owned" do
    assert {:named_argument_mismatch, :positional_after_named, details} =
             error!("""
             mod NamedMisplaced
               fn pair(a: Int, b: Int) -> Int = a + b
               fn bad() -> Int = pair(a: 1, 2)
             end
             """)

    assert details.argument_index == 1
    assert Enum.at(details.argument_spans, 1).start_line == 3
  end

  test "unknown and duplicate names retain authored label ranges" do
    assert {:named_argument_mismatch, :unknown_label, unknown} =
             error!("""
             mod NamedUnknown
               fn pair(a: Int, b: Int) -> Int = a + b
               fn bad() -> Int = pair(a: 1, nope: 2)
             end
             """)

    assert unknown.label == "nope"
    assert Enum.at(unknown.label_spans, 1).start_line == 3
    assert unknown.parameter_spans != []

    assert {:named_argument_mismatch, :duplicate_label, duplicate} =
             error!("""
             mod NamedDuplicate
               fn pair(a: Int, b: Int) -> Int = a + b
               fn bad() -> Int = pair(a: 1, a: 2)
             end
             """)

    assert duplicate.label == "a"
  end

  test "a named gap reports the omitted required prefix parameter" do
    assert {:named_argument_mismatch, :missing_label, details} =
             error!("""
             mod NamedGap
               fn pair(a: Int, b: Int) -> Int = a + b
               fn bad() -> Int = pair(b: 2)
             end
             """)

    assert details.label == "a"
    assert details.parameter_index == 0
  end

  test "reordering happens before dependent implicit solving" do
    module =
      compile!("""
      mod NamedDependent
        fn choose({a: Type}, fallback: a, value: a) -> a = value
        fn go() -> Int = choose(value: 7, fallback: 5)
      end
      """)

    assert apply(module, :go, []) == 7
  end

  test "constructor alignment preserves bidirectional checking for lambda fields" do
    assert {:ok, _env} =
             Program.elaborate("""
             mod NamedConstructorLambda
               type Token = Step
               type Maybe(a: Type) = None | Some(a)
               type Box(a: Type) = Box(Token -> Maybe(a))
               fn empty() -> Box(Int) = Box(fn(_) -> None())
             end
             """)
  end

  test "overload pruning aligns each candidate independently of source order" do
    module =
      compile!("""
      mod NamedOverload
        fn choose(left x: Int, right y: Bool) -> Int = x
        fn choose(left x: Bool, right y: Int) -> Int = y + 100
        fn first() -> Int = choose(right: true, left: 7)
        fn second() -> Int = choose(right: 8, left: false)
      end
      """)

    assert apply(module, :first, []) == 7
    assert apply(module, :second, []) == 108
  end

  test "partial application keeps the aligned telescope prefix" do
    module =
      compile!("""
      mod NamedPartial
        fn digits(a: Int, b: Int, c: Int) -> Int = a * 100 + b * 10 + c
        fn partial() -> (Int) -> Int = digits(b: 2, a: 1)
        fn go() -> Int = partial()(3)
      end
      """)

    assert apply(module, :go, []) == 123
  end

  test "constructor calls disambiguate field-like names from typed patterns in expression position" do
    module =
      compile!("""
      mod NamedConstructor
        type Pair indices (tag: Nat)
          MkPair : (left: Int) -> (right: Int) -> Pair(Z)
        fn sum(pair: Pair(Z)) -> Int = match pair
          MkPair(left, right) -> left * 10 + right
        fn go() -> Int = sum(MkPair(right: 2, left: 1))
      end
      """)

    assert apply(module, :go, []) == 12
  end

  test "interface methods and constrained dictionary calls share named-argument alignment" do
    module =
      compile!("""
      mod NamedDictionary
        interface Pick(a)
          fn pick(first: a, second: a) -> a
        implementation Pick for Int
          fn pick(first: Int, second: Int) -> Int = first
        fn constrained({a: Type}, first: a, second: a) -> a where Pick(a) = pick(first: first, second: second)
        fn go() -> Int = constrained(second: 2, first: 1)
      end
      """)

    assert apply(module, :go, []) == 1
  end
end
