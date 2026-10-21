defmodule Cure.Core.AdmissionBoundaryAuditTest do
  @moduledoc """
  Executable controls for the conservative proof boundary. These tests pin
  implementation behavior; they do not prove Elixir/Agda refinement or turn
  syntax support into type checking.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Eval, Grade, Inductive, Kernel}

  @g Grade.unrestricted()
  @atom {:atom_type}
  @packed {:data, :"Boundary#Packed", [], [@atom]}
  @value {:ctor, :"Boundary#Pack", [@atom, {:atom_lit, :payload}]}

  setup do
    family = Inductive.family(:Packed, [], [{:A, {:type, 0}}], 1)
    ctor = Inductive.ctor(:Pack, [{:A, {:type, 0}}, {:x, {:var, 0}}], [{:var, 1}])

    env =
      Env.empty()
      |> Env.with_owner("Boundary")
      |> Inductive.declare(family, [ctor])
      |> Env.add_def(:answer, @atom, {:atom_lit, :answer})

    family = Inductive.get_family(env, :"Boundary#Packed")
    ctor = Inductive.get_ctor(env, :"Boundary#Pack")
    assert :ok = Kernel.check_family(env, family)
    assert :ok = Kernel.check_ctor(env, family, ctor)
    assert :ok = Kernel.check_def(env, :"Boundary#answer")

    {:ok, env: env, ctx: Context.empty(env)}
  end

  defp motive do
    {:lam, @g, {:type, 0}, {:lam, @g, {:data, :"Boundary#Packed", [], [{:var, 0}]}, {:var, 1}}}
  end

  test "the Atom-only dependent fixture checks its original goal before evaluation", %{ctx: ctx} do
    program = {:case, @value, motive(), [{:"Boundary#Pack", 2, {:var, 0}}]}

    assert :ok = Kernel.check(ctx, @value, Eval.eval(@packed, []))
    assert :ok = Kernel.check(ctx, program, {:vatom_type})
    assert {:ok, {:vatom_type}} = Kernel.infer(ctx, program)
    assert {:vatom, :payload} = Eval.eval(program, [])
    assert :ok = Kernel.check(ctx, {:atom_lit, :payload}, {:vatom_type})
  end

  test "canonical keys remain exact while bare names follow the current owner", %{env: env} do
    other =
      env
      |> Env.with_owner("Other")
      |> Inductive.declare(
        Inductive.family(:Packed, [], [{:A, {:type, 0}}], 1),
        [Inductive.ctor(:Pack, [{:A, {:type, 0}}, {:x, {:var, 0}}], [{:var, 1}])]
      )

    assert %{name: :"Boundary#Pack"} = Inductive.get_ctor(other, :"Boundary#Pack")
    assert %{name: :"Other#Pack"} = Inductive.get_ctor(other, :Pack)
    assert :"Other#Packed" = Inductive.ctor_family(other, :Pack)
    assert :"Boundary#Packed" = Inductive.ctor_family(other, :"Boundary#Pack")

    ambiguous = Env.with_owner(other, nil)
    assert nil == Inductive.get_ctor(ambiguous, :Pack)
    assert nil == Inductive.get_family(ambiguous, :Packed)
    assert nil == Inductive.get_ctor(env, :"Foreign#Pack")
  end

  test "constructor enumeration preserves declaration order rather than map-key order", %{env: env} do
    env =
      Inductive.declare(
        env,
        Inductive.family(:Ordered, [], [], 0),
        [Inductive.ctor(:Zulu, [], []), Inductive.ctor(:Alpha, [], [])]
      )

    assert [%{name: :"Boundary#Zulu"}, %{name: :"Boundary#Alpha"}] =
             Inductive.ctors_of(env, :"Boundary#Ordered")
  end

  test "replacing a global does not change the original snapshot or captured context", %{env: env, ctx: ctx} do
    changed = Env.add_def(env, :answer, @atom, {:atom_lit, :replacement})

    assert :ok = Kernel.check_def(changed, :"Boundary#answer")
    assert %{body: {:atom_lit, :answer}} = Env.get_def(env, :"Boundary#answer")
    assert %{body: {:atom_lit, :replacement}} = Env.get_def(changed, :"Boundary#answer")
    assert %{body: {:atom_lit, :answer}} = Env.get_def(Context.signature(ctx), :"Boundary#answer")
    assert {:vneutral, {:nglobal, :"Boundary#answer"}} = Eval.eval({:global, :"Boundary#answer"}, [])
  end

  test "Any checking is directional subtyping, not definitional equality", %{env: env} do
    env =
      env
      |> Inductive.declare(Inductive.opaque_family(:Any, [], 0), [])
      |> Inductive.register_builtin(:any, :"Boundary#Any")

    assert :ok = Kernel.check(Context.empty(env), {:atom_lit, :payload}, {:vdata, :"Boundary#Any", []})
    refute Conv.conv_values?({:vatom_type}, {:vdata, :"Boundary#Any", []}, 0, env)

    ctx = Context.extend(Context.empty(env), {:vdata, :"Boundary#Any", []})
    assert {:error, _reason} = Kernel.check(ctx, {:var, 0}, {:vatom_type})
  end

  test "List lifts Any widening without equating the two family applications", %{env: env} do
    env =
      env
      |> Inductive.declare(Inductive.opaque_family(:Any, [], 0), [])
      |> Inductive.register_builtin(:any, :"Boundary#Any")
      |> Inductive.declare(Inductive.family(:List, [{:A, {:type, 0}}], [], 1), [])
      |> Inductive.register_builtin(:list, :"Boundary#List")

    narrow = {:vdata, :"Boundary#List", [{:vatom_type}]}
    wide = {:vdata, :"Boundary#List", [{:vdata, :"Boundary#Any", []}]}

    assert :ok = Kernel.check(Context.extend(Context.empty(env), narrow), {:var, 0}, wide)
    assert {:error, _reason} = Kernel.check(Context.extend(Context.empty(env), wide), {:var, 0}, narrow)
    refute Conv.conv_values?(narrow, wide, 0, env)
  end

  test "opaque families cannot use vacuous coverage as an empty eliminator", %{env: env} do
    env = Inductive.declare(env, Inductive.opaque_family(:Carrier, [], 0), [])
    carrier = {:data, :"Boundary#Carrier", [], []}
    ctx = Context.extend(Context.empty(env), Eval.eval(carrier, []))
    program = {:case, {:var, 0}, {:lam, @g, carrier, {:type, 0}}, []}

    assert {:error, :opaque_not_eliminable} = Kernel.infer(ctx, program)
  end

  test "kernel effect-bind acceptance retains the continuation grade", %{ctx: ctx} do
    for grade <- [Grade.one(), Grade.affine(), Grade.unrestricted()] do
      continuation = {:lam, grade, @atom, {:effect_pure, {:var, 0}}}
      program = {:effect_bind, {:effect_pure, {:atom_lit, :payload}}, continuation}

      assert {:ok, {:veffect_type, {:vatom_type}}} = Kernel.infer(ctx, program)
      assert :ok = Kernel.check(ctx, program, {:veffect_type, {:vatom_type}})
    end
  end

  test "Float payloads remain distinguishable despite sharing a type", %{ctx: ctx, env: env} do
    assert :ok = Kernel.check(ctx, {:float_lit, 0.5}, {:vfloat_type})
    assert :ok = Kernel.check(ctx, {:float_lit, 0.25}, {:vfloat_type})
    refute Conv.conv?({:float_lit, 0.5}, {:float_lit, 0.25}, [], 0, env)
  end

  test "fresh binders use levels while let binders retain their actual values", %{ctx: ctx} do
    opaque = Context.extend(ctx, {:vatom_type})
    defined = Context.extend_def(ctx, {:vatom_type}, {:vatom, :outer})
    mixed = Context.extend(defined, {:vatom_type})

    assert [{:vneutral, {:nvar, 0}}] = Context.env(opaque)
    assert [{:vatom, :outer}] = Context.env(defined)
    assert [{:vneutral, {:nvar, 1}}, {:vatom, :outer}] = Context.env(mixed)
    assert {:vatom, :outer} = Eval.eval({:var, 1}, Context.env(mixed))
    assert {:ok, {:vatom_type}} = Kernel.infer(mixed, {:var, 1})
  end

  test "branch fields do not displace a captured outer let value", %{ctx: ctx} do
    body =
      {:case, @value, {:lam, @g, {:type, 0}, {:lam, @g, @packed, @atom}},
       [
         {:"Boundary#Pack", 2, {:var, 2}}
       ]}

    program = {:let, @g, @atom, {:atom_lit, :outer}, body}
    assert :ok = Kernel.check(ctx, program, {:vatom_type})
    assert {:vatom, :outer} = Eval.eval(program, [])
  end
end
