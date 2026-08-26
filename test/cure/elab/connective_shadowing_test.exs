defmodule Cure.Elab.ConnectiveShadowingTest do
  @moduledoc """
  Emit's connective/projection inlining must key off the DEF RECORD — the
  `Std.Bool`/`Std.Sigma` import path marks `inline_hint` on the prelude defs —
  never the bare global atom. Under shadowing the LOCAL def owns the bare key
  (the shadowed import moves to its `Mod#name` re-key), so an atom-keyed
  inline would miscompile a user `eq(Int, Int) -> Int` to BEAM `:==` and a
  user `sigma_first(Int) -> Int` to `element(1, _)`. Same R1 discipline as
  the builtin-op registry: no marker on the record, no inline.
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.{Emit, Program}

  @src """
  mod M
    fn eq(a: Int, b: Int) -> Int = a
    fn sigma_first(x: Int) -> Int = x + 1
    fn t_eq() -> Int = eq(1, 2)
    fn t_sf() -> Int = sigma_first(3)
  end
  """

  test "user defs shadowing `eq`/`sigma_first` are called, not inlined" do
    {:ok, env} = Program.elaborate(@src)

    {:ok, mod} =
      Emit.compile_and_load(env,
        module: :"Cure.ConnShadow",
        functions: [:eq, :sigma_first, :t_eq, :t_sf]
      )

    assert apply(mod, :t_eq, []) == 1
    assert apply(mod, :t_sf, []) == 4
  end

  test "the emitted forms carry calls to the shadowing defs, no :== op" do
    {:ok, env} = Program.elaborate(@src)
    forms = Emit.module_forms(env, :"Cure.ConnShadowForms", [:eq, :sigma_first, :t_eq, :t_sf])

    refute :== in collect_ops(forms)
    assert calls_global?(forms, :eq)
    assert calls_global?(forms, :sigma_first)
  end

  defp collect_ops(form) when is_tuple(form) do
    case form do
      {:op, _line, op, _a, _b} -> [op | form |> Tuple.to_list() |> Enum.flat_map(&collect_ops/1)]
      {:op, _line, op, _a} -> [op | form |> Tuple.to_list() |> Enum.flat_map(&collect_ops/1)]
      _ -> form |> Tuple.to_list() |> Enum.flat_map(&collect_ops/1)
    end
  end

  defp collect_ops(list) when is_list(list), do: Enum.flat_map(list, &collect_ops/1)
  defp collect_ops(_), do: []

  defp calls_global?(form, name) when is_tuple(form) do
    case form do
      {:call, _l, {:atom, _l2, ^name}, _args} -> true
      _ -> form |> Tuple.to_list() |> Enum.any?(&calls_global?(&1, name))
    end
  end

  defp calls_global?(list, name) when is_list(list), do: Enum.any?(list, &calls_global?(&1, name))
  defp calls_global?(_, _name), do: false
end
