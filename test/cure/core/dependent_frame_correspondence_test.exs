defmodule Cure.Core.DependentFrameCorrespondenceTest do
  @moduledoc """
  Bounded evidence for the proposed forward-dependent spine/frame interface.
  Declarations and positive programs are kernel-checked before evaluation.
  This is not an Agda-to-Elixir refinement theorem or coverage of erased slots.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Grade, Inductive, Kernel}

  @carrier {:atom_type}
  @g Grade.unrestricted()
  @packed {:data, :FramePacked, [], [@carrier]}

  setup do
    packed = Inductive.family(:FramePacked, [], [{:A, {:type, 0}}], 1)
    pack = Inductive.ctor(:FramePack, [{:A, {:type, 0}}, {:x, {:var, 0}}], [{:var, 1}])
    param_box = Inductive.family(:FrameParamBox, [{:A, {:type, 0}}], [], 1)

    box =
      Inductive.ctor(:FrameBox, [{:x, {:var, 0}}], [], [:unrestricted], [{:var, 1}])

    dual = Inductive.family(:FrameDual, [{:A, {:type, 0}}, {:B, {:type, 0}}], [], 1)

    pair =
      Inductive.ctor(
        :FramePair,
        [{:x, {:var, 1}}, {:y, {:var, 1}}],
        [],
        [:unrestricted, :unrestricted],
        [{:var, 3}, {:var, 2}]
      )

    indexed = Inductive.family(:FrameIndexed, [{:A, {:type, 0}}], [{:x, {:var, 0}}], 1)
    witness = Inductive.ctor(:FrameWitness, [{:x, {:var, 0}}], [{:var, 0}], [:unrestricted], [{:var, 1}])
    computed_index = {:app, {:lam, @g, {:var, 1}, {:var, 0}}, {:var, 0}}

    computed =
      Inductive.ctor(:FrameComputed, [{:x, {:var, 0}}], [computed_index], [:unrestricted], [{:var, 1}])

    env =
      Env.empty()
      |> Inductive.declare(packed, [pack])
      |> Inductive.declare(param_box, [box])
      |> Inductive.declare(dual, [pair])
      |> Inductive.declare(indexed, [witness, computed])

    assert :ok = Kernel.check_family(env, packed)
    assert :ok = Kernel.check_ctor(env, packed, pack)
    assert :ok = Kernel.check_family(env, param_box)
    assert :ok = Kernel.check_ctor(env, param_box, box)

    assert :ok = Kernel.check_family(env, dual)
    assert :ok = Kernel.check_ctor(env, dual, pair)
    assert :ok = Kernel.check_family(env, indexed)
    assert :ok = Kernel.check_ctor(env, indexed, witness)
    assert :ok = Kernel.check_ctor(env, indexed, computed)

    {:ok, ctx: Context.empty(env), dual: dual, indexed: indexed}
  end

  test "a scoped field declaration still needs a valid kind", %{ctx: ctx} do
    family = Inductive.family(:FrameBadKind, [], [], 2)
    constructor = Inductive.ctor(:FrameBadKindCtor, [{:x, {:type, 2}}], [])
    env = Inductive.declare(Context.signature(ctx), family, [constructor])

    assert :ok = Kernel.check_family(env, family)
    assert {:error, :universe_ceiling} = Kernel.check_ctor(env, family, constructor)
  end

  defp packed(value), do: {:ctor, :FramePack, [@carrier, {:atom_lit, value}]}

  # λ(A : Type0). λ(p : Packed A). A
  defp unpack_motive do
    {:lam, @g, {:type, 0}, {:lam, @g, {:data, :FramePacked, [], [{:var, 0}]}, {:var, 1}}}
  end

  test "preceding fields instantiate later field types and the result index", %{ctx: ctx} do
    assert {:ok, {:vdata, :FramePacked, [{:vatom_type}]}} = Kernel.infer(ctx, packed(:payload))
    assert :ok = Kernel.check(ctx, packed(:payload), Eval.eval(@packed, []))
  end

  test "a dependent case binds the last field at zero", %{ctx: ctx} do
    program = {:case, packed(:payload), unpack_motive(), [{:FramePack, 2, {:var, 0}}]}

    assert {:ok, {:vatom_type}} = Kernel.infer(ctx, program)
    assert {:vatom, :payload} = Eval.eval(program, [])
  end

  test "the first field remains available separately from the dependent value", %{ctx: ctx} do
    motive =
      {:lam, @g, {:type, 0}, {:lam, @g, {:data, :FramePacked, [], [{:var, 0}]}, {:type, 0}}}

    program = {:case, packed(:payload), motive, [{:FramePack, 2, {:var, 1}}]}

    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx, program)
    assert {:vatom_type} = Eval.eval(program, [])
  end

  test "a lambda keeps its own binder while capturing the last branch field", %{ctx: ctx} do
    motive =
      {:lam, @g, {:type, 0}, {:lam, @g, {:data, :FramePacked, [], [{:var, 0}]}, {:pi, @g, @carrier, {:var, 2}}}}

    body = {:lam, @g, @carrier, {:var, 1}}
    program = {:case, packed(:payload), motive, [{:FramePack, 2, body}]}

    assert :ok = Kernel.check(ctx, program, Eval.eval({:pi, @g, @carrier, @carrier}, []))
    assert {:vatom, :payload} = Eval.apply(Eval.eval(program, []), {:vatom, :ambient})
  end

  test "an ambient value remains outside both field slots", %{ctx: ctx} do
    motive = {:lam, @g, {:type, 0}, {:lam, @g, {:data, :FramePacked, [], [{:var, 0}]}, @carrier}}
    branch = {:FramePack, 2, {:var, 2}}
    program = {:let, @g, @carrier, {:atom_lit, :ambient}, {:case, packed(:payload), motive, [branch]}}

    assert {:ok, {:vatom_type}} = Kernel.infer(ctx, program)
    assert {:vatom, :ambient} = Eval.eval(program, [])
  end

  test "a mismatched dependent value is rejected", %{ctx: ctx} do
    bad = {:ctor, :FramePack, [@carrier, {:float_lit, 0.5}]}
    assert {:error, _reason} = Kernel.infer(ctx, bad)
  end

  test "reversing the surface argument order is rejected", %{ctx: ctx} do
    assert {:error, _reason} = Kernel.infer(ctx, {:ctor, :FramePack, [{:atom_lit, :payload}, @carrier]})
  end

  test "missing and surplus fields fail the actual constructor arity check", %{ctx: ctx} do
    for args <- [[@carrier], [@carrier, {:atom_lit, :payload}, {:atom_lit, :ambient}]] do
      assert {:error, :ctor_arity} = Kernel.infer(ctx, {:ctor, :FramePack, args})
    end
  end

  test "expected parameters seed field checking without becoming branch fields", %{ctx: ctx} do
    constructor = {:ctor, :FrameBox, [{:atom_lit, :payload}]}
    goal = {:data, :FrameParamBox, [@carrier], []}

    assert :ok = Kernel.check(ctx, constructor, Eval.eval(goal, []))

    program =
      {:let, @g, goal, constructor, {:case, {:var, 0}, {:lam, @g, goal, @carrier}, [{:FrameBox, 1, {:var, 0}}]}}

    assert {:ok, {:vatom_type}} = Kernel.infer(ctx, program)
    assert {:vatom, :payload} = Eval.eval(program, [])

    wrong_goal = {:data, :FrameParamBox, [{:float_type}], []}
    assert {:error, _reason} = Kernel.check(ctx, constructor, Eval.eval(wrong_goal, []))
  end

  test "two distinct parameter types seed two fields without reversing surface order", %{ctx: ctx} do
    goal = {:data, :FrameDual, [@carrier, {:float_type}], []}
    constructor = {:ctor, :FramePair, [{:atom_lit, :payload}, {:float_lit, 0.5}]}

    assert :ok = Kernel.check(ctx, constructor, Eval.eval(goal, []))

    first =
      {:let, @g, goal, constructor, {:case, {:var, 0}, {:lam, @g, goal, @carrier}, [{:FramePair, 2, {:var, 1}}]}}

    last =
      {:let, @g, goal, constructor, {:case, {:var, 0}, {:lam, @g, goal, {:float_type}}, [{:FramePair, 2, {:var, 0}}]}}

    assert {:ok, {:vatom_type}} = Kernel.infer(ctx, first)
    assert {:vatom, :payload} = Eval.eval(first, [])
    assert {:ok, {:vfloat_type}} = Kernel.infer(ctx, last)
    assert {:vfloat, 0.5} = Eval.eval(last, [])
  end

  test "swapping distinct expected parameter types rejects the same field values", %{ctx: ctx} do
    constructor = {:ctor, :FramePair, [{:atom_lit, :payload}, {:float_lit, 0.5}]}
    wrong_goal = {:data, :FrameDual, [{:float_type}, @carrier], []}

    assert {:error, _reason} = Kernel.check(ctx, constructor, Eval.eval(wrong_goal, []))
  end

  test "a result index depends on the checked parameter and field", %{ctx: ctx} do
    constructor = {:ctor, :FrameWitness, [{:atom_lit, :payload}]}
    goal = {:data, :FrameIndexed, [@carrier], [{:atom_lit, :payload}]}
    wrong_goal = {:data, :FrameIndexed, [@carrier], [{:atom_lit, :different}]}

    assert :ok = Kernel.check(ctx, constructor, Eval.eval(goal, []))
    assert {:error, _reason} = Kernel.check(ctx, constructor, Eval.eval(wrong_goal, []))
  end

  test "a computed dependent result index is instantiated before conversion", %{ctx: ctx} do
    constructor = {:ctor, :FrameComputed, [{:atom_lit, :payload}]}
    goal = {:data, :FrameIndexed, [@carrier], [{:atom_lit, :payload}]}
    wrong_goal = {:data, :FrameIndexed, [@carrier], [{:atom_lit, :different}]}

    assert :ok = Kernel.check(ctx, constructor, Eval.eval(goal, []))
    assert {:error, _reason} = Kernel.check(ctx, constructor, Eval.eval(wrong_goal, []))
  end

  test "scoped but swapped result parameters fail uniformity", %{ctx: ctx, dual: dual} do
    constructor =
      Inductive.ctor(
        :FrameNonUniform,
        [{:x, {:var, 1}}, {:y, {:var, 1}}],
        [],
        [:unrestricted, :unrestricted],
        [{:var, 2}, {:var, 3}]
      )

    assert {:error, {:non_uniform_parameter, %{position: 0}}} =
             Kernel.check_ctor(Context.signature(ctx), dual, constructor)
  end

  test "a result index must type-check under the declared parameter and field", %{ctx: ctx, indexed: indexed} do
    constructor =
      Inductive.ctor(
        :FrameBadIndex,
        [{:x, {:var, 0}}],
        [{:float_lit, 0.5}],
        [:unrestricted],
        [{:var, 1}]
      )

    assert {:error, _reason} = Kernel.check_ctor(Context.signature(ctx), indexed, constructor)
  end
end
