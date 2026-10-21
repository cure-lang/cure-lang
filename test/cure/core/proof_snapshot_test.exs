defmodule Cure.Core.ProofSnapshotTest do
  @moduledoc """
  Capture/render controls for the bounded proof snapshot. Agda independently
  replays the exact generated fixture; neither side certifies the extractor.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Env, Eval, Grade, Inductive, Kernel, ProofSnapshot, Term}
  alias Cure.Test.ProofSnapshotFixture

  @fixture Path.expand("../../..", __DIR__) <> "/proof/Fixtures/ExecutableSnapshot.agda"
  @pack :"Boundary#Pack"
  @packed :"Boundary#Packed"

  setup do
    {:ok, env: ProofSnapshotFixture.environment()}
  end

  test "the generated nonempty dependent fixture is byte-for-byte reproducible", %{env: env} do
    family = Inductive.get_family(env, @packed)
    assert :ok = Kernel.check_family(env, family)

    for ctor <- Inductive.ctors_of(env, @packed), do: assert(:ok = Kernel.check_ctor(env, family, ctor))
    for name <- Map.keys(env.defs), do: assert(:ok = Kernel.check_def(env, name))

    assert {:ok, generated} = ProofSnapshot.to_agda(env, "Fixtures.ExecutableSnapshot")
    assert generated == File.read!(@fixture)

    assert {:ok, %{"families" => [%{"constructors" => [first, second]}], "globals" => [_, _, _, _]}} =
             ProofSnapshot.capture(env)

    assert first["name"] == "Boundary#Pack"
    assert second["name"] == "Boundary#Alternate"
  end

  test "the computed constructor case retains the original Atom goal", %{env: env} do
    %{body: {:case, {:ctor, @pack, args}, motive, branches}} = Env.get_def(env, :"Boundary#unpack")
    program = {:case, {:ctor, :"Boundary#Alternate", args}, motive, branches}

    assert :ok = Kernel.check(Context.empty(env), program, {:vatom_type})
    assert {:ok, {:vatom_type}} = Kernel.infer(Context.empty(env), program)
    assert {:vatom, :payload} = Eval.eval(program, [])
  end

  test "capture success does not discharge published kinds or hidden body goals", %{env: env} do
    bad_kind = Env.add_def(env, :bad_kind, {:type, 2}, {:atom_lit, :payload})
    assert {:ok, _snapshot} = ProofSnapshot.capture(bad_kind)
    assert {:error, :universe_ceiling} = Kernel.check_def(bad_kind, :"Boundary#bad_kind")

    bad_body = Env.add_def(env, :bad_body, {:float_type}, {:atom_lit, :payload})
    refute Env.certified?(bad_body, :"Boundary#bad_body")
    assert {:ok, _snapshot} = ProofSnapshot.capture(bad_body)
    assert {:error, _reason} = Kernel.check_def(bad_body, :"Boundary#bad_body")
  end

  test "raw hidden bodies and certification claims remain distinct", %{env: env} do
    assert {:ok, %{"globals" => globals}} = ProofSnapshot.capture(env)
    held = Enum.find(globals, &(&1["name"] == "Boundary#held"))
    answer = Enum.find(globals, &(&1["name"] == "Boundary#answer"))

    assert %{"body" => %{"node" => "atom_lit", "value" => "hidden"}, "certified" => false} = held
    assert %{"certified" => true, "totality_certified" => true} = answer
    refute Env.certified?(env, :"Boundary#held")
    assert Env.certified?(env, :"Boundary#answer")
  end

  test "map insertion order does not affect exported bytes", %{env: env} do
    reversed = %{
      env
      | defs: env.defs |> Enum.reverse() |> Map.new(),
        ctors: env.ctors |> Enum.reverse() |> Map.new(),
        families: env.families |> Enum.reverse() |> Map.new()
    }

    assert ProofSnapshot.to_agda(env, "Fixtures.ExecutableSnapshot") ==
             ProofSnapshot.to_agda(reversed, "Fixtures.ExecutableSnapshot")
  end

  test "capture does not convert syntax support into typing or certification", %{env: env} do
    bad = {:app, {:atom_lit, :not_a_function}, {:atom_lit, :argument}}
    env = Env.add_def(env, :ill_typed, {:atom_type}, bad)

    assert {:ok, _snapshot} = ProofSnapshot.capture(env)
    assert {:error, _reason} = Kernel.check(Context.empty(env), bad, {:vatom_type})
    refute Env.certified?(env, :"Boundary#ill_typed")
  end

  test "opaque and builtin registries are excluded rather than erased", %{env: env} do
    opaque = Inductive.declare(env, Inductive.opaque_family(:Carrier, [], 0), [])
    assert {:error, %{reason: :unsupported_opaque_family}} = ProofSnapshot.capture(opaque)

    builtin = Inductive.register_builtin(env, :any, @packed)
    assert {:error, %{reason: :unsupported_builtins}} = ProofSnapshot.capture(builtin)
  end

  test "primitive extern and unknown metadata are rejected", %{env: env} do
    assert {:error, %{reason: :unsupported_primitives}} = ProofSnapshot.capture(%{env | primitives: %{op: :op}})

    extern = Env.add_def(env, :external, {:atom_type}, {:extern, {:erlang, :make_ref, 0}})
    assert {:error, %{reason: :malformed_term}} = ProofSnapshot.capture(extern)

    marked = update_in(env.defs[:"Boundary#answer"], &Map.put(&1, :builtin_op, :add))
    assert {:error, %{reason: :unsupported_metadata}} = ProofSnapshot.capture(marked)
  end

  test "all registered bodies are scanned even when hidden or unreachable", %{env: env} do
    for term <- [
          {:hole, "hidden"},
          {:absurd},
          {:float_lit, 0.5},
          {:int_type},
          {:int_lit, -1},
          {:nat_lit, 0},
          {:bounded_lit, 0},
          {:effect_type, {:atom_type}},
          {:effect_pure, {:atom_lit, :payload}},
          {:effect_bind, {:effect_pure, {:atom_lit, :payload}}, {:hole, "continuation"}}
        ] do
      changed = Env.add_def(env, :hidden_unsupported, {:atom_type}, term)
      assert {:error, %{reason: :unsupported_term}} = ProofSnapshot.capture(changed)
    end
  end

  test "unsupported nodes under binders and branches cannot hide", %{env: env} do
    for term <- [
          {:lam, Grade.zero(), {:atom_type}, {:float_lit, 0.5}},
          {:let, Grade.zero(), {:atom_type}, {:hole, "erased"}, {:var, 0}},
          {:case, {:ctor, @pack, [{:atom_type}, {:atom_lit, :payload}]}, {:atom_type},
           [{@pack, 2, {:lam, Grade.unrestricted(), {:atom_type}, {:float_lit, 0.5}}}]}
        ] do
      changed = Env.add_def(env, :nested, {:atom_type}, term)
      assert {:error, %{reason: :unsupported_term}} = ProofSnapshot.capture(changed)
    end
  end

  test "constructor quantities plicities and vector arities are explicit exclusions", %{env: env} do
    for {field, value, reason} <- [
          {:quantities, [Grade.zero(), Grade.unrestricted()], :unsupported_layout},
          {:quantities, [Grade.unrestricted()], :layout_arity},
          {:plicities, [:implicit, :explicit], :unsupported_layout},
          {:plicities, [], :layout_arity}
        ] do
      changed = update_in(env.ctors[@pack], &Map.put(&1, field, value))
      assert {:error, %{reason: ^reason}} = ProofSnapshot.capture(changed)
    end
  end

  test "global quantity metadata cannot be silently dropped", %{env: env} do
    changed =
      Env.add_def(
        env,
        :graded,
        {:pi, Grade.unrestricted(), {:atom_type}, {:atom_type}},
        {:lam, Grade.unrestricted(), {:atom_type}, {:var, 0}},
        [Grade.zero()]
      )

    assert {:error, %{reason: :unsupported_layout}} = ProofSnapshot.capture(changed)
  end

  test "parameters seed dependent fields without becoming runtime constructor slots", %{env: env} do
    box = Inductive.family(:Box, [{:A, {:type, 0}}], [], 1)
    ctor = Inductive.ctor(:BoxValue, [{:x, {:var, 0}}], [], [Grade.unrestricted()], [{:var, 1}])
    type = {:data, :"Boundary#Box", [{:atom_type}], []}
    fields_only = {:ctor, :"Boundary#BoxValue", [{:atom_lit, :payload}]}

    env =
      env
      |> Inductive.declare(box, [ctor])
      |> Env.add_def(:box_value, type, fields_only)

    assert :ok = Kernel.check_family(env, Inductive.get_family(env, :"Boundary#Box"))

    assert :ok =
             Kernel.check_ctor(
               env,
               Inductive.get_family(env, :"Boundary#Box"),
               Inductive.get_ctor(env, :"Boundary#BoxValue")
             )

    assert :ok = Kernel.check_def(env, :"Boundary#box_value")
    assert {:ok, _snapshot} = ProofSnapshot.capture(env)

    explicit_prefix = {:ctor, :"Boundary#BoxValue", [{:atom_type}, {:atom_lit, :payload}]}
    assert :ok = Kernel.check(Context.empty(env), explicit_prefix, Cure.Core.Eval.eval(type, []))

    assert {:error, %{reason: :unsupported_constructor_spine}} =
             ProofSnapshot.capture(Env.add_def(env, :box_value, type, explicit_prefix))
  end

  test "result-vector arities are checked independently of term scoping", %{env: env} do
    assert {:error, %{reason: :result_index_arity}} =
             ProofSnapshot.capture(put_in(env.ctors[@pack][:result_indices], []))

    assert {:error, %{reason: :result_parameter_arity}} =
             ProofSnapshot.capture(put_in(env.ctors[@pack][:result_params], [{:atom_type}]))
  end

  test "constructor order must be complete unique and consistent with ownership", %{env: env} do
    for order <- [[], [@pack], [@pack, @pack], [@pack, :"Foreign#Ctor"]] do
      changed = put_in(env.families[@packed][:ctor_order], order)
      assert {:error, %{reason: :inconsistent_constructor_order}} = ProofSnapshot.capture(changed)
    end

    changed = %{env | ctor_to_family: Map.delete(env.ctor_to_family, @pack)}
    assert {:error, %{reason: :inconsistent_owner_keys}} = ProofSnapshot.capture(changed)

    changed = put_in(env.ctor_to_family[@pack], :"Foreign#Family")
    assert {:error, %{reason: :unknown_owner}} = ProofSnapshot.capture(changed)
  end

  test "map keys and embedded identities must agree", %{env: env} do
    for changed <- [
          put_in(env.families[@packed][:name], :"Boundary#Wrong"),
          put_in(env.ctors[@pack][:name], :"Boundary#Wrong"),
          put_in(env.defs[:"Boundary#answer"][:name], :"Boundary#Wrong")
        ] do
      assert {:error, %{reason: :key_name_mismatch}} = ProofSnapshot.capture(changed)
    end
  end

  test "bare aliases and unknown canonical references are not resolved implicitly", %{env: env} do
    for {reference, reason} <- [
          {{:global, :answer}, :noncanonical_name},
          {{:global, :"Foreign#answer"}, :unknown_reference},
          {{:ctor, :Pack, []}, :noncanonical_name}
        ] do
      changed = Env.add_def(env, :alias, {:atom_type}, reference)
      assert {:error, %{reason: ^reason}} = ProofSnapshot.capture(changed)
    end

    changed = %{env | qualified_aliases: %{{"Alias", :answer, :value} => :"Boundary#answer"}}
    assert {:error, %{reason: :unsupported_aliases}} = ProofSnapshot.capture(changed)
  end

  test "escaped declaration result and branch variables are rejected", %{env: env} do
    changed = put_in(env.ctors[@pack][:args], [{:A, {:type, 0}}, {:x, {:var, 1}}])
    assert {:error, %{reason: :escaped_variable}} = ProofSnapshot.capture(changed)

    changed = put_in(env.ctors[@pack][:result_indices], [{:var, 2}])
    assert {:error, %{reason: :escaped_variable}} = ProofSnapshot.capture(changed)

    body = {:case, {:ctor, @pack, [{:atom_type}, {:atom_lit, :payload}]}, {:atom_type}, [{@pack, 2, {:var, 2}}]}
    assert {:error, %{reason: :escaped_variable}} = ProofSnapshot.capture(Env.add_def(env, :escape, {:atom_type}, body))
  end

  test "missing data indices parameter prefixes and branch arities are not normalized away", %{env: env} do
    for {term, reason} <- [
          {{:data, @packed, [], []}, :data_arity},
          {{:ctor, @pack, [{:atom_type}]}, :unsupported_constructor_spine},
          {{:ctor, @pack, [{:atom_type}, {:atom_type}, {:atom_lit, :payload}]}, :unsupported_constructor_spine},
          {{:case, {:atom_lit, :payload}, {:atom_type}, [{@pack, 1, {:var, 0}}]}, :branch_arity}
        ] do
      assert {:error, %{reason: ^reason}} = ProofSnapshot.capture(Env.add_def(env, :arity, {:atom_type}, term))
    end
  end

  test "certificate flags do not create absent bodies or refer to unknown globals", %{env: env} do
    changed = %{env | certified: MapSet.put(env.certified, :"Foreign#missing")}
    assert {:error, %{reason: :unknown_certified_global}} = ProofSnapshot.capture(changed)

    changed = %{env | totality_certified: MapSet.new()}
    assert {:error, %{reason: :inconsistent_certification}} = ProofSnapshot.capture(changed)

    changed = put_in(env.defs[:"Boundary#answer"][:body], nil)
    assert {:error, %{reason: :certified_body_missing}} = ProofSnapshot.capture(changed)

    total_only = %{env | certified: MapSet.new()}
    assert {:ok, %{"globals" => globals}} = ProofSnapshot.capture(total_only)

    assert %{"certified" => false, "totality_certified" => true} =
             Enum.find(globals, &(&1["name"] == "Boundary#answer"))
  end

  test "a low-level certification flag is retained as a claim rather than proved totality", %{env: env} do
    recursive =
      env
      |> Env.add_def(:loop, {:atom_type}, {:global, :"Boundary#loop"})
      |> Env.certify(:loop)

    assert :ok = Kernel.check_def(recursive, :"Boundary#loop")
    assert {:ok, %{"globals" => globals}} = ProofSnapshot.capture(recursive)

    assert %{"certified" => true, "body" => %{"node" => "global", "name" => "Boundary#loop"}} =
             Enum.find(globals, &(&1["name"] == "Boundary#loop"))
  end

  test "ASCII string escaping is lossless and module names cannot inject declarations", %{env: env} do
    literal = :"quote\"\\slash"
    changed = Env.add_def(env, :quoted, {:atom_type}, {:atom_lit, literal})
    assert {:ok, source} = ProofSnapshot.to_agda(changed, "Fixtures.Quoted")
    assert source =~ ~S("quote\"\\slash")
    assert {:ok, snapshot} = ProofSnapshot.capture(changed)
    global = Enum.find(snapshot["globals"], &(&1["name"] == "Boundary#quoted"))
    assert {:atom_lit, ^literal} = Term.from_external(global["body"])

    assert {:error, %{reason: :invalid_module_name}} = ProofSnapshot.to_agda(env, "Fixtures.X\npostulate Bad : Set")

    assert {:error, %{reason: :unsupported_name_encoding}} =
             ProofSnapshot.capture(Env.add_def(env, :unicode, {:atom_type}, {:atom_lit, :català}))
  end

  test "noncanonical registry keys and malformed certificate sets are excluded", %{env: env} do
    bare = Env.add_def(Env.empty(), :bare, {:atom_type}, {:atom_lit, :payload})
    assert {:error, %{reason: :noncanonical_name}} = ProofSnapshot.capture(bare)
    assert {:error, %{reason: :malformed_certificate_set}} = ProofSnapshot.capture(%{env | certified: nil})
    assert {:error, %{reason: :malformed_certificate_set}} = ProofSnapshot.capture(%{env | totality_certified: []})
  end

  test "malformed entry tables return structured errors", %{env: env} do
    for changed <- [
          %{env | families: []},
          %{env | ctors: []},
          %{env | defs: []},
          %{env | builtins: []}
        ] do
      assert {:error, %{reason: :malformed_table}} = ProofSnapshot.capture(changed)
    end

    assert {:error, %{reason: :malformed_environment}} = ProofSnapshot.capture(%{})
    assert {:error, %{reason: :malformed_entry}} = ProofSnapshot.capture(put_in(env.families[@packed], nil))

    assert {:error, %{reason: :missing_metadata}} =
             ProofSnapshot.capture(update_in(env.families[@packed], &Map.delete(&1, :ctor_order)))
  end
end
