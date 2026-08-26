defmodule Cure.Compiler.ShapeInterfaceReloadPropertyTest do
  use ExUnit.Case, async: true

  @moduletag :tmp_dir

  test "large-elimination interpretation is definitionally stable after interface-only reload", %{
    tmp_dir: dir
  } do
    provider =
      write!(
        dir,
        "provider.cure",
        """
        mod Shape.Provider
          use Std.Option

          type Choice(a: Type, b: Type) = This(a) | That(b)
          type Shape = IntC | BoolC | PairC(Shape, Shape) | ChoiceC(Shape, Shape) | OptionC(Shape) | ListC(Shape)

          @reducible
          fn Sem(shape: Shape) -> Type = match shape
            IntC() -> Int
            BoolC() -> Bool
            PairC(left, right) -> Tuple(Sem(left), Sem(right))
            ChoiceC(left, right) -> Choice(Sem(left), Sem(right))
            OptionC(inner) -> Option(Sem(inner))
            ListC(inner) -> List(Sem(inner))
        """
      )

    consumer =
      write!(
        dir,
        "consumer.cure",
        """
        mod Shape.Consumer
          use Shape.Provider
          use Std.Option

          fn nested() -> Sem(ListC(BoolC)) = [true, false]
          fn nested_pair() -> Sem(PairC(IntC, ListC(BoolC))) = %[7, [true, false]]
          fn nested_choice() -> Sem(ChoiceC(IntC, BoolC)) = That(true)
          fn nested_option() -> Sem(OptionC(ListC(IntC))) = Some([1, 2])

          fn keep({shape: Shape}, value: Sem(shape)) -> Sem(shape) = value
        """
      )

    interfaces = Path.join(dir, "interfaces")

    assert {:ok, same_run} = check([consumer, provider], dir)
    assert :ok = Cure.Compiler.ModulePipeline.kernel_verify_interfaces(same_run)

    assert {:ok, checked_provider} = check([provider], dir)
    assert :ok = Cure.Compiler.ModulePipeline.write_interfaces(checked_provider, interfaces)

    assert {:ok, stdlib} =
             Cure.Compiler.Artifacts.open_verified_set(
               kind: :stdlib,
               candidates: Cure.Stdlib.Paths.beam_dirs()
             )

    assert {:ok, loaded_interfaces} =
             Cure.Compiler.ModulePipeline.Interface.load_roots([interfaces, stdlib.artifact_root])

    assert %Cure.Compiler.ModuleInterface{} =
             reloaded_interface = Map.fetch!(loaded_interfaces, "Shape.Provider")

    assert {:ok, reloaded_env} =
             Cure.Compiler.ModulePipeline.Interface.to_env(reloaded_interface)

    assert Cure.Core.Env.certified?(reloaded_env, :"Shape.Provider#Sem")
    File.rm!(provider)

    assert {:ok, checked_consumer} =
             check([consumer], dir,
               interface_roots: [interfaces],
               forbid_source_fallback: true,
               forbid_beam_resolution: true,
               fresh_environment: true
             )

    assert :ok = Cure.Compiler.ModulePipeline.kernel_verify_interfaces(checked_consumer)
    assert_shape_index_erased!(checked_consumer.beams[:"Cure.Shape.Consumer"])
  end

  defp assert_shape_index_erased!(beam) do
    {:ok, {_, [{:exports, exports}]}} = :beam_lib.chunks(beam, [:exports])
    assert {:keep, 1} in exports
    refute {:keep, 2} in exports

    {:beam_file, _, _, _, _, functions} = :beam_disasm.file(beam)

    instructions =
      for {:function, :keep, 1, _label, body} <- functions,
          instruction <- body,
          do: instruction

    encoded = :erlang.term_to_binary(instructions)
    refute encoded =~ "IntC"
    refute encoded =~ "BoolC"
    refute encoded =~ "PairC"
    refute encoded =~ "ChoiceC"
    refute encoded =~ "OptionC"
    refute encoded =~ "ListC"
  end

  defp check(paths, root, opts \\ []) do
    {:ok, stdlib} =
      Cure.Compiler.Artifacts.open_verified_set(
        kind: :stdlib,
        candidates: Cure.Stdlib.Paths.beam_dirs()
      )

    interface_roots =
      (Keyword.get(opts, :interface_roots, []) ++ [stdlib.artifact_root])
      |> Enum.uniq()

    Cure.Compiler.ModulePipeline.check(
      paths,
      Keyword.merge(
        [
          module_pipeline: :canonical,
          package: "shape-property",
          source_roots: [root],
          products: [:beams]
        ],
        Keyword.put(opts, :interface_roots, interface_roots)
      )
    )
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
