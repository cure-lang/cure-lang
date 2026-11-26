defmodule Antigen.Phase5EffectTypingProbeTest do
  use ExUnit.Case, async: true

  alias Antigen.{Challenge, Corpus}
  alias Antigen.Assays.KernelProbe, as: Assay
  alias Antigen.Backend.StreamData, as: Backend
  alias Antigen.Generators.KernelProbe, as: Generator
  alias Cure.Core.{Context, Conv, Env, Eval, Kernel, Normalise}

  @atom {:atom_type}
  @binary {:binary_type}
  @value {:atom_lit, :ok}
  @pure {:effect_pure, @value}
  @continuation {:lam, :unrestricted, @atom, {:effect_pure, {:var, 0}}}
  @bind {:effect_bind, @pure, @continuation}
  @effect_atom {:veffect_type, {:vatom_type}}
  @effect_binary {:veffect_type, {:vbinary_type}}

  test "closed formation, pure and bind have their real inferred and checked types" do
    ctx = Context.empty(Env.empty())
    assert {:ok, {:vtype, {:finite, %{constant: 0, atoms: []}}}} = Kernel.infer(ctx, {:effect_type, @atom})
    assert {:ok, @effect_atom} = Kernel.infer(ctx, @pure)
    assert {:ok, @effect_atom} = Kernel.infer(ctx, @bind)
    assert :ok = Kernel.check(ctx, @pure, Eval.eval({:effect_type, @atom}, []))
    assert :ok = Kernel.check(ctx, @bind, Eval.eval({:effect_type, @atom}, []))

    linear = {:effect_bind, @pure, {:lam, :linear, @atom, {:effect_pure, {:var, 0}}}}
    assert {:ok, @effect_atom} = Kernel.infer(ctx, linear)
    assert :ok = Kernel.check(ctx, linear, @effect_atom)
  end

  test "each malformed effect premise reaches its intended stable typing guard" do
    ctx = Context.empty(Env.empty())
    assert {:error, :not_a_type} = Kernel.infer(ctx, {:effect_type, @value})
    assert {:error, :effect_bind_not_effect} = Kernel.infer(ctx, {:effect_bind, @value, @continuation})
    assert {:error, :not_a_function} = Kernel.infer(ctx, {:effect_bind, @pure, @value})

    assert {:error, :effect_bind_domain_mismatch} =
             Kernel.infer(ctx, {:effect_bind, @pure, {:lam, :unrestricted, @binary, {:effect_pure, {:var, 0}}}})

    assert {:error, :effect_bind_cont_not_effect} =
             Kernel.infer(ctx, {:effect_bind, @pure, {:lam, :unrestricted, @atom, {:var, 0}}})

    assert {:error, :effect_bind_result_mismatch} = Kernel.check(ctx, @bind, @effect_binary)
    assert {:error, {:conversion_failure, @atom, @binary}} = Kernel.check(ctx, @pure, @effect_binary)

    for term <- [@pure, @bind] do
      assert {:error, {:conversion_failure, {:effect_type, @atom}, @atom}} =
               Kernel.check(ctx, term, {:vatom_type})
    end
  end

  test "typing does not add a monad reduction or collapse the inert effect signature" do
    ctx = Context.empty(Env.empty())
    assert Normalise.nf(ctx, @bind) == @bind
    assert Conv.conv?(@bind, @bind, [], 0, Context.signature(ctx))
    refute Conv.conv?(@bind, {:app, @continuation, @value}, [], 0, Context.signature(ctx))
    refute Conv.conv?(@bind, @pure, [], 0, Context.signature(ctx))
  end

  test "exactly one recipe is appended after the conserved original57 prefix" do
    inventory = File.read!("test/antigen/fixtures/phase5_kernel_recipe_replacements.json") |> :json.decode()
    rename = Map.new(inventory["replacements"], &{&1["old_tag"], &1["new_tag"]})
    expected = Enum.map(inventory["old_advertised_tags"], &Map.get(rename, &1, &1))
    assert length(expected) == 57
    cells = Generator.cover_cells()
    assert Enum.map(Enum.take(cells, 57), fn {"kernel/probe", tag} -> Atom.to_string(tag) end) == expected
    assert Enum.drop(cells, 57) == [{"kernel/probe", :effect_typing_guards}]

    sampled = Backend.sample_seeded(Generator.gen(), 1000, 20_261_126)
    assert Enum.any?(sampled, &(&1.payload.probe == :effect_typing_guards))
    assert :ok = Assay.run(probe())
  end

  test "the bounded public-judgment recipe survives the current corpus carrier" do
    challenge = probe()
    assert :ok = Assay.run(challenge)
    assert {:ok, replayed} = challenge |> Corpus.encode_record() |> Corpus.decode_record()
    assert :ok = Assay.run(replayed)
  end

  test "the banked recipe retains its identity and no historical covered threshold was lowered" do
    ledger =
      "test/antigen/fixtures/phase5_effect_typing_coverage_addition.json"
      |> File.read!()
      |> :json.decode()

    assert ledger["covered_floors_unchanged"]
    assert ledger["records_after"] == ledger["records_before"] + 1

    assert [record] =
             Antigen.CoverageBaseline.coverage_path()
             |> Corpus.record_lines()
             |> Enum.filter(&(Corpus.raw_key(&1) == ledger["key"]))

    assert Base.encode16(:crypto.hash(:sha256, record), case: :lower) == ledger["record_sha256"]
    assert {:ok, challenge} = Corpus.decode_record(record)
    assert challenge.payload.probe == :effect_typing_guards
    assert :ok = Assay.run(challenge)
    assert {:ok, floor} = Antigen.CoverageBaseline.read_baseline()

    modules = Map.new(Antigen.Cover.cover_modules(), &{inspect(&1), &1})
    assert MapSet.new(Map.keys(ledger["covered_floors"])) == MapSet.new(Map.keys(modules))

    for {name, old_covered} <- ledger["covered_floors"] do
      assert floor[Map.fetch!(modules, name)].covered >= old_covered
    end
  end

  @tag :tmp_dir
  test "fresh VM decodes the explicitly supplied pool atom and replays the recipe", %{tmp_dir: root} do
    path = Path.join(root, "effect-recipe.sexp")
    File.write!(path, Corpus.encode_record(probe()))
    paths = :code.get_path() |> Enum.flat_map(&["-pa", &1 |> List.to_string() |> Path.expand()])

    script = """
    {:ok, challenge} = Antigen.Corpus.decode_record(File.read!(hd(System.argv())))
    :effect_typing_guards = challenge.payload.probe
    :ok = Antigen.Assays.KernelProbe.run(challenge)
    IO.inspect(:ok)
    """

    {output, 0} =
      System.cmd(System.find_executable("elixir"), ["--erl", "+S 2:2"] ++ paths ++ ["-e", script, "--", path])

    assert String.trim(output) == ":ok"
  end

  defp probe do
    Challenge.new(
      kind: :kernel_probe,
      assay: "kernel/probe",
      label: :probe,
      payload: %{probe: :effect_typing_guards}
    )
  end
end
