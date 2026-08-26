defmodule Cure.Elab.LetEmitTest do
  @moduledoc """
  The Core `:let` binder survives erasure and lowers to a real BEAM binding —
  `begin L = <val>, <body> end` — so the right-hand side is evaluated **once**
  regardless of how many times the variable is used.

  This is the honest end of the bind-once claim: not "the Core term has one
  occurrence" (asserted in `Cure.Elab.LetBindOnceTest`) but "the emitted bytecode
  binds once and computes the right answer". Compiled with `:compile.forms`,
  loaded, and executed.
  """
  use ExUnit.Case, async: false
  alias Cure.Elab.{Emit, Program}

  @src """
  fn double(n: Int) -> Int =
    let m = n + n
    m + m
  fn once(n: Int) -> Int =
    let m = n + 1
    m
  fn unused(n: Int) -> Int =
    let m = n + 1
    n
  fn nested(n: Int) -> Int =
    let a = n + 1
    let b = a + a
    b + a
  """

  setup_all do
    {:ok, env} = Program.elaborate(@src)

    {:ok, mod} =
      Emit.compile_and_load(env,
        module: :"Cure.LetEmitTest.M",
        functions: [:double, :once, :unused, :nested]
      )

    on_exit(fn ->
      :code.purge(mod)
      :code.delete(mod)
    end)

    %{mod: mod, env: env}
  end

  test "a let used twice computes correctly through real BEAM", %{mod: mod} do
    # double(5) = let m = 10 in m + m = 20
    assert mod.double(5) == 20
    assert mod.double(0) == 0
    assert mod.double(-3) == -12
  end

  test "a let used once, and one never used, still compute correctly", %{mod: mod} do
    assert mod.once(41) == 42
    assert mod.unused(41) == 41
  end

  test "chained lets compute correctly", %{mod: mod} do
    # a = 6, b = 12, b + a = 18
    assert mod.nested(5) == 18
  end

  test "the emitted forms bind the rhs once, not per use site", %{env: env} do
    {:ok, forms} = Emit.compile_forms(env, :"Cure.LetEmitTest.Forms", [:double])

    double_form =
      Enum.find(forms, fn
        {:function, _, :double, 1, _} -> true
        _ -> false
      end)

    refute is_nil(double_form), "no `double/1` function form emitted"

    # One `=` binding for the let; the `+` that computes `n + n` appears once.
    assert count(double_form, :match) == 1
    assert count_op(double_form, :+) == 2, "one `+` for the rhs, one for `m + m`"
  end

  defp count(form, tag) when is_tuple(form) do
    self = if elem(form, 0) == tag, do: 1, else: 0
    self + (form |> Tuple.to_list() |> Enum.reduce(0, &(count(&1, tag) + &2)))
  end

  defp count(list, tag) when is_list(list), do: Enum.reduce(list, 0, &(count(&1, tag) + &2))
  defp count(_, _), do: 0

  defp count_op(form, op) when is_tuple(form) do
    self = if match?({:op, _, ^op, _, _}, form), do: 1, else: 0
    self + (form |> Tuple.to_list() |> Enum.reduce(0, &(count_op(&1, op) + &2)))
  end

  defp count_op(list, op) when is_list(list), do: Enum.reduce(list, 0, &(count_op(&1, op) + &2))
  defp count_op(_, _), do: 0
end
