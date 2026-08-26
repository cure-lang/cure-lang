defmodule Cure.Stdlib.NatToIntegerTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Program
  @moduletag :stdlib

  test "to_integer is a total structural fold, not an FFI boundary" do
    src = """
    mod ToIntegerClient
      use Std.Nat
      fn three() -> Int = to_integer(S(S(S(Z()))))
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    # Guard: to_integer must have a real body (structural), not an @extern stub.
    to_int =
      Enum.find(Map.values(env.defs), fn d ->
        is_map(d) and Map.get(d, :name) |> to_string() |> String.ends_with?("to_integer")
      end)

    assert to_int != nil
    assert Map.get(to_int, :body) not in [nil, :extern]
  end
end
