defmodule Antigen.Phase5BoolMenuRecipeTest do
  use ExUnit.Case, async: false

  alias Antigen.{CanonBuiltins, Challenge, Corpus}
  alias Antigen.Assays.KernelProbe, as: Assay
  alias Antigen.Backend.StreamData, as: Backend
  alias Antigen.Generators.{DepMatch, KernelProbe, Malformed, Primitive, SigMenu}
  alias Cure.Core.{Builtins, Context, Conv, Env, Eval, Inductive, Kernel, Normalise, Serialize}

  @false_ctor :"Std.Bool#False"
  @true_ctor :"Std.Bool#True"
  @bool {:data, :Bool, [], []}
  @nat {:data, :Nat, [], []}
  @zero {:ctor, :Z, []}
  @one {:ctor, :S, [@zero]}
  @old [
    :sort_value_type_formers,
    :cert_dangling_callee,
    :serialize_malformed_symbol,
    :eval_nondata_scrutinee,
    :check_ctor_arity,
    :check_bounded_tower
  ]
  @new [
    :typed_value_type_motives,
    :cert_unresolved_callee,
    :serialize_current_malformed_symbol,
    :eval_float_scrutinee,
    :check_canonical_ctor_arity,
    :check_canonical_bounded_tower
  ]
  @fixture "test/antigen/fixtures/phase5_kernel_recipe_replacements.json"

  test "both synthetic menus retain bare Bool but declare exactly the canonical two constructors" do
    for env <- menus() do
      assert Inductive.builtin(env, :bool) == :Bool
      assert Enum.map(Inductive.ctors_of(env, :Bool), & &1.name) == [@false_ctor, @true_ctor]
      refute Map.has_key?(env.ctors, :False)
      refute Map.has_key?(env.ctors, :True)
      assert :ok = Builtins.validate!(env, :bool, :Bool)

      for ctor <- Inductive.ctors_of(env, :Bool) do
        assert :ok = Kernel.check_ctor(env, Inductive.get_family(env, :Bool), ctor)
      end
    end
  end

  test "all comparison folds remain typed and stable in both menus" do
    for env <- menus(),
        {prefix, literal} <- [{"int", &{:int_lit, &1}}, {"float", &{:float_lit, &1 / 1}}],
        op <- [:lt, :le, :gt, :ge, :eq, :ne],
        {left, right} <- [{0, 0}, {0, 1}, {1, 0}] do
      # The operation set is closed and already declared by Builtins.
      global = String.to_existing_atom(prefix <> "_" <> Atom.to_string(op))
      term = app2(global, literal.(left), literal.(right))
      ctx = Context.empty(env)
      assert {:ok, {:vdata, :Bool, []}} = Kernel.infer(ctx, term)
      assert {:ctor, ctor, []} = nf = Normalise.nf(ctx, term)
      assert ctor in [@false_ctor, @true_ctor]
      assert :ok = Kernel.check(ctx, nf, Eval.eval(@bool, []))
      assert Normalise.nf(ctx, nf) == nf
    end
  end

  test "comparison cases and explicit Bool beta/iota reduce without relaxing coverage or conversion" do
    for env <- menus() do
      ctx = Context.empty(env)
      motive = {:lam, :unrestricted, @bool, @nat}
      branches = [{@false_ctor, 0, @one}, {@true_ctor, 0, @zero}]
      body = {:case, {:var, 0}, motive, branches}

      for {ctor, expected} <- [{@true_ctor, @zero}, {@false_ctor, @one}] do
        term = {:app, {:lam, :unrestricted, @bool, body}, {:ctor, ctor, []}}
        assert {:ok, {:vdata, :Nat, []}} = Kernel.infer(ctx, term)
        assert Eval.eval(term, []) == Eval.eval(expected, [])
        assert Normalise.nf(ctx, term) == expected
      end

      for {right, expected} <- [{0, @zero}, {1, @one}] do
        term = {:case, app2(:int_eq, {:int_lit, 0}, {:int_lit, right}), motive, branches}
        assert {:ok, {:vdata, :Nat, []}} = Kernel.infer(ctx, term)
        assert Normalise.nf(ctx, term) == expected
      end

      assert {:error, :coverage} =
               Kernel.infer(ctx, {:case, app2(:int_eq, {:int_lit, 0}, {:int_lit, 0}), motive, [{@false_ctor, 0, @one}]})

      refute Conv.conv_values?(Eval.eval({:ctor, @true_ctor, []}, []), Eval.eval({:ctor, @false_ctor, []}, []), 0, env)
    end
  end

  test "lookup aliases alone cannot repair comparison-case iota" do
    env = SigMenu.env_of(:v1)

    bare = %{
      env
      | ctors: Map.drop(env.ctors, [@false_ctor, @true_ctor]),
        ctor_to_family: Map.drop(env.ctor_to_family, [@false_ctor, @true_ctor])
    }

    bare =
      Inductive.declare(bare, Inductive.get_family(env, :Bool), [
        Inductive.ctor(:False, [], []),
        Inductive.ctor(:True, [], [])
      ])

    aliases =
      Enum.reduce([False: @false_ctor, True: @true_ctor], bare, fn {old, canonical}, acc ->
        %{
          acc
          | ctors: Map.put(acc.ctors, canonical, Map.fetch!(acc.ctors, old)),
            ctor_to_family: Map.put(acc.ctor_to_family, canonical, :Bool)
        }
      end)

    ctx = Context.empty(aliases)
    comparison = app2(:int_eq, {:int_lit, 0}, {:int_lit, 0})
    assert :ok = Kernel.check(ctx, Normalise.nf(ctx, comparison), Eval.eval(@bool, []))
    term = {:case, comparison, {:lam, :unrestricted, @bool, @nat}, [{:False, 0, @one}, {:True, 0, @zero}]}
    assert Normalise.nf(ctx, term) == term
    refute Eval.constructor_name_matches?(:True, @true_ctor)
  end

  test "explicit legacy migration must rename constructor values and branch identities together" do
    motive = {:lam, :unrestricted, @bool, @nat}
    old_branches = [{:False, 0, @one}, {:True, 0, @zero}]
    current_branches = [{@false_ctor, 0, @one}, {@true_ctor, 0, @zero}]

    assert_raise RuntimeError, ~r/ι: no branch/, fn ->
      Eval.eval({:case, {:ctor, @true_ctor, []}, motive, old_branches}, [])
    end

    assert_raise RuntimeError, ~r/ι: no branch/, fn ->
      Eval.eval({:case, {:ctor, :True, []}, motive, current_branches}, [])
    end

    migrated = {:case, {:ctor, @true_ctor, []}, motive, current_branches}
    assert {:ok, {:vdata, :Nat, []}} = Kernel.infer(Context.empty(SigMenu.env_of(:v1)), migrated)
    assert Eval.eval(migrated, []) == Eval.eval(@zero, [])
  end

  test "primitive sampler normalization rechecks instead of merely returning a qualified spelling" do
    cases = Backend.sample_seeded(Primitive.gen(), 500, 20_261_125)
    assert length(cases) == 500
    for challenge <- cases, do: assert(:ok = Antigen.Assays.Term.run(challenge))
    assert length(DepMatch.case_variants()) == 36
    assert length(Malformed.cover_cells()) == 17
  end

  test "six old recipes are inert and only the distinct approved tags are live and portable" do
    inventory = File.read!(@fixture) |> :json.decode()
    refute inventory["automatic_dispatch"]
    assert length(inventory["replacements"]) == 6
    advertised = KernelProbe.cover_cells()
    rename = Map.new(inventory["replacements"], &{&1["old_tag"], &1["new_tag"]})
    expected = Enum.map(inventory["old_advertised_tags"], &Map.get(rename, &1, &1))

    assert Enum.take(advertised, length(expected))
           |> Enum.map(fn {"kernel/probe", tag} -> Atom.to_string(tag) end) == expected

    assert Enum.drop(advertised, length(expected)) == [{"kernel/probe", :effect_typing_guards}]

    for {old, current} <- Enum.zip(@old, @new) do
      refute {"kernel/probe", old} in advertised
      assert {"kernel/probe", current} in advertised
      archived = Enum.find(inventory["replacements"], &(&1["old_tag"] == Atom.to_string(old)))
      assert archived["new_tag"] == Atom.to_string(current)
      assert digest(archived["old_evaluator_source"]) == archived["old_evaluator_sha256"]
      assert digest(archived["old_oracle_source"]) == archived["old_oracle_sha256"]
      assert {:violation, {:retired_kernel_probe, ^old}} = Assay.run(probe(old))
      assert {:error, _} = probe(old) |> Corpus.encode_record() |> Corpus.decode_record()
      assert :ok = Assay.run(probe(current))
      assert {:ok, replayed} = probe(current) |> Corpus.encode_record() |> Corpus.decode_record()
      assert :ok = Assay.run(replayed)
    end

    for {"kernel/probe", tag} <- advertised, do: assert(:ok = Assay.run(probe(tag)))
  end

  test "typed value-type motives use the real Bool identity and context witnesses" do
    env = Builtins.seed(Env.empty())
    bool = Inductive.builtin(env, :bool)

    for {type, value} <- [{{:binary_type}, {:vbinary_type}}, {{:atom_type}, {:vatom_type}}] do
      ctx = Context.empty(env) |> Context.extend(value) |> Context.extend(Kernel.bool_type_value(env))
      motive = {:lam, :unrestricted, {:data, bool, [], []}, type}
      branches = Enum.map(Inductive.ctors_of(env, bool), &{&1.name, 0, {:var, 1}})
      assert {:ok, _} = Kernel.infer(ctx, motive)
      assert {:ok, ^value} = Kernel.infer(ctx, {:case, {:var, 0}, motive, branches})
    end
  end

  test "unresolved certification rejects while the typed completed closure accepts" do
    env = Builtins.seed(Env.empty())
    nat = {:data, Inductive.builtin(env, :nat), [], []}
    type = {:pi, :unrestricted, nat, nat}

    unresolved =
      env
      |> Env.add_def(:f, type, {:lam, :unrestricted, nat, {:app, {:global, :g}, {:var, 0}}})
      |> Env.add_def(:g, type, {:lam, :unrestricted, nat, {:app, {:global, :h}, {:var, 0}}})

    assert {:error, _} = Kernel.check_def(unresolved, :g)
    refute Cure.Elab.TotalityClosure.provably_total?(unresolved, :f)
    complete = Env.add_def(unresolved, :h, type, {:lam, :unrestricted, nat, {:var, 0}})
    for name <- [:f, :g, :h], do: assert(:ok = Kernel.check_def(complete, name))
    assert Cure.Elab.TotalityClosure.provably_total?(complete, :f)
  end

  test "current malformed-symbol decoding and Float scrutinee target their actual guards" do
    good = Serialize.encode({:atom_lit, :ok})
    assert {:ok, {:atom_lit, :ok}} = Serialize.decode(good)
    assert {:error, :malformed_symbol} = good |> String.replace("(atom ok)", "(atom 5)") |> Serialize.decode()
    assert {:error, :incompatible_core_format} = Serialize.decode("(atom 5)")

    assert_raise RuntimeError, ~r/ι: non-data scrutinee/, fn ->
      Eval.eval({:case, {:float_lit, 3.0}, {:lam, :unrestricted, @nat, @nat}, [{:Z, 0, @zero}]}, [])
    end

    assert_raise RuntimeError, ~r/ι: no branch for constructor :FromNat/, fn ->
      Eval.eval({:case, {:int_lit, 3}, {:lam, :unrestricted, @nat, @nat}, [{:Z, 0, @zero}]}, [])
    end
  end

  test "canonical constructor arity reaches that guard rather than foreign-family rejection" do
    env = Builtins.seed(Env.empty())
    ctx = Context.empty(env)
    {zero, successor} = nat_constructors(env)
    z = {:ctor, zero, []}
    assert {:error, :ctor_arity} = Kernel.check(ctx, {:ctor, successor, [z, z]}, Kernel.nat_type_value(env))
    assert :ok = Kernel.check(ctx, {:ctor, successor, [z]}, Kernel.nat_type_value(env))
    assert {:error, {:foreign_ctor, :S}} = Kernel.check(ctx, {:ctor, :S, [@zero, @zero]}, Eval.eval(@nat, []))
  end

  test "registered semantic Nat towers discriminate valid and out-of-range ordinals" do
    env = Builtins.seed(Env.empty())
    nat = Inductive.builtin(env, :nat)
    {zero, successor} = nat_constructors(env)

    env =
      env
      |> Inductive.declare(
        Inductive.family(:Bounded, [], [n: {:data, nat, [], []}], Cure.Core.Sort.finite_closed(0)),
        []
      )
      |> Inductive.register_builtin(:bounded, :Bounded)

    ctx = Context.empty(env)
    goal = {:vdata, :Bounded, [{:vctor, successor, [{:vctor, zero, []}]}]}
    assert :ok = Kernel.check(ctx, {:bounded_lit, 0}, goal)
    assert {:error, {:bounded_lit_out_of_range, 1, 1}} = Kernel.check(ctx, {:bounded_lit, 1}, goal)

    assert {:error, {:bounded_bound_not_concrete, _}} =
             Kernel.check(ctx, {:bounded_lit, 0}, {:vdata, :Bounded, [{:vctor, :S, [{:vctor, :Z, []}]}]})
  end

  @tag :tmp_dir
  test "fresh VM decodes both Bool constructor names and replays every new recipe", %{tmp_dir: root} do
    records = Enum.map([@false_ctor, @true_ctor], &Corpus.encode_record(Challenge.stub({:ctor, &1, []})))
    records = records ++ Enum.map(@new, &Corpus.encode_record(probe(&1)))
    path = Path.join(root, "current-recipes.sexp")
    File.write!(path, Enum.join(records, "\n") <> "\n")
    paths = :code.get_path() |> Enum.flat_map(&["-pa", &1 |> List.to_string() |> Path.expand()])

    script = """
    results = Antigen.Corpus.stream(hd(System.argv())) |> Enum.to_list()
    8 = length(results)
    Enum.each(results, fn result ->
      {:ok, challenge} = result
      if challenge.kind == :kernel_probe, do: :ok = Antigen.Assays.KernelProbe.run(challenge)
    end)
    IO.inspect(:ok)
    """

    {output, 0} =
      System.cmd(System.find_executable("elixir"), ["--erl", "+S 2:2"] ++ paths ++ ["-e", script, "--", path])

    assert String.trim(output) == ":ok"
  end

  defp menus do
    [SigMenu.env_of(:v1), CanonBuiltins.seed(Env.empty(), bool: true) |> Builtins.seed_ops()]
  end

  defp app2(global, left, right), do: {:app, {:app, {:global, global}, left}, right}

  defp nat_constructors(env) do
    ctors = Inductive.ctors_of(env, Inductive.builtin(env, :nat))

    {Enum.find(ctors, &(Cure.Elab.Name.base(&1.name) == "Z")).name,
     Enum.find(ctors, &(Cure.Elab.Name.base(&1.name) == "S")).name}
  end

  defp probe(tag), do: Challenge.new(kind: :kernel_probe, assay: "kernel/probe", label: :probe, payload: %{probe: tag})
  defp digest(bytes), do: :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)
end
