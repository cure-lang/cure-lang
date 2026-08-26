defmodule Cure.Elab.BoolConnectiveCodegenTest do
  @moduledoc """
  Phase 3 of retiring the Boolean-connective primitives: even though the surface
  connectives now elaborate to APPLICATIONS of the `Std.Bool` prelude defs
  (`and`/`or`/`not`/`eq`/`ne`), a SATURATED application must
  still lower to the native BEAM boolean op — byte-for-byte the primitive's old
  codegen (strict `:and`/`:or`/`:not`; `:==`/`:"/="` for Bool equality). The
  telltale sign of inlining: the compiled module needs no connective def call
  and still runs.
  """
  use ExUnit.Case, async: false

  alias Cure.Elab.{Emit, Program}

  @src """
  mod M
    use Std.Bool
    fn a_ff() -> Bool = true and false
    fn a_tt() -> Bool = true and true
    fn o_ft() -> Bool = false or true
    fn n_t() -> Bool = not true
    fn eq_tt() -> Bool = true == true
    fn ne_tf() -> Bool = true != false
  end
  """

  test "saturated connective apps inline to native BEAM ops and evaluate correctly" do
    {:ok, env} = Program.elaborate(@src)

    fns = [:a_ff, :a_tt, :o_ft, :n_t, :eq_tt, :ne_tf]
    {:ok, mod} = Emit.compile_and_load(env, module: :"Cure.BoolConnCodegen", functions: fns)

    assert apply(mod, :a_ff, []) == false
    assert apply(mod, :a_tt, []) == true
    assert apply(mod, :o_ft, []) == true
    assert apply(mod, :n_t, []) == false
    assert apply(mod, :eq_tt, []) == true
    assert apply(mod, :ne_tf, []) == true
  end

  test "the emitted forms use the native boolean ops, not calls to the defs" do
    {:ok, env} = Program.elaborate(@src)
    forms = Emit.module_forms(env, :"Cure.BoolConnForms", [:a_ff, :n_t, :eq_tt])

    ops = collect_ops(forms)
    assert :and in ops
    assert :not in ops
    assert :== in ops
    refute calls_global?(forms, :and)
    refute calls_global?(forms, :not)
    refute calls_global?(forms, :eq)
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
