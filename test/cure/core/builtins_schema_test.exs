defmodule Cure.Core.BuiltinsSchemaTest do
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Builtins}

  defp declare_family(env, fname, ctors) do
    family = %{name: fname, params: [], indices: [], level: 0}

    ctor_maps =
      Enum.map(ctors, fn {cname, arg_types} ->
        %{
          name: cname,
          args: arg_types,
          result_indices: [],
          result_params: [],
          quantities: List.duplicate(:unrestricted, length(arg_types))
        }
      end)

    Inductive.declare(env, family, ctor_maps)
  end

  test "a well-formed Bool passes validation" do
    env = declare_family(Env.empty(), :Bool, [{:False, []}, {:True, []}])
    assert :ok = Builtins.validate!(env, :bool, :Bool)
  end

  test "Bool with wrong constructor names is rejected" do
    env = declare_family(Env.empty(), :Coin, [{:Heads, []}, {:Tails, []}])

    assert_raise ArgumentError, ~r/expected constructors/, fn ->
      Builtins.validate!(env, :bool, :Coin)
    end
  end

  test "Bool with wrong arity is rejected" do
    env = declare_family(Env.empty(), :Bad, [{:False, []}, {:True, [{:n, {:data, :Bad, [], []}}]}])

    assert_raise ArgumentError, ~r/arity|nullary|expected constructors/, fn ->
      Builtins.validate!(env, :bool, :Bad)
    end
  end

  test "a well-formed Nat passes validation" do
    env = declare_family(Env.empty(), :Nat, [{:Z, []}, {:S, [{:n, {:data, :Nat, [], []}}]}])
    assert :ok = Builtins.validate!(env, :nat, :Nat)
  end
end
