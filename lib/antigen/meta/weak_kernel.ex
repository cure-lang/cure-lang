defmodule Antigen.Meta.WeakKernel do
  @moduledoc """
  Sensitivity meta-testing support (Run C spec §3). `real/0` is the identity map:
  every kernel op bound to its real `Cure.Core.*` capture. `weaken/1` returns
  `real/0` with exactly one rule (or, for `:universe_accepts_all`, the three
  `check_*` rules) replaced by a deliberately **too-permissive** stub — a
  simulated soundness hole. The real kernel is never modified; weakenings are used
  only by the sensitivity meta-test, injected through each assay's `run/2` seam.
  """
  alias Cure.Core.{Kernel, Conv, Inductive, Eval}

  @spec real() :: map()
  def real do
    %{
      infer: &Kernel.infer/2,
      check: &Kernel.check/3,
      conv_within: &Conv.conv_within?/6,
      positive?: &Inductive.positive?/2,
      check_def: &Kernel.check_def/2,
      check_family: &Kernel.check_family/2,
      check_ctor: &Kernel.check_ctor/3
    }
  end

  @spec weaken(atom()) :: map()
  def weaken(:infer_accepts_all),
    do: %{real() | infer: fn _ctx, _t -> {:ok, Eval.eval({:type, 0}, [])} end}

  # real infer, but on success return a type value distinct from any well-typed
  # term's real type in the catalog fixture (Type 0 ≠ Nat), so a real `check`
  # against it disagrees. Passes kernel errors through untouched.
  def weaken(:infer_wrong_type) do
    %{
      real()
      | infer: fn ctx, t ->
          case Kernel.infer(ctx, t) do
            {:ok, _v} -> {:ok, Eval.eval({:type, 0}, [])}
            err -> err
          end
        end
    }
  end

  def weaken(:check_accepts_all), do: %{real() | check: fn _ctx, _t, _ty -> :ok end}
  def weaken(:positive_accepts_all), do: %{real() | positive?: fn _env, _fam -> :ok end}

  def weaken(:universe_accepts_all) do
    %{
      real()
      | check_def: fn _env, _dn -> :ok end,
        check_family: fn _env, _fam -> :ok end,
        check_ctor: fn _env, _fam, _ctor -> :ok end
    }
  end

  def weaken(:conv_always_true),
    do: %{real() | conv_within: fn _t, _tp, _e, _d, _s, _f -> {:ok, true} end}

  def weaken(:conv_exhausts_fuel),
    do: %{real() | conv_within: fn _t, _tp, _e, _d, _s, _f -> :fuel_exhausted end}
end
