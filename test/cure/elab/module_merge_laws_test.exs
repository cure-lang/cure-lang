defmodule Cure.Elab.ModuleMergeLawsTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  @moduletag :tmp_dir

  setup %{tmp_dir: dir} do
    previous = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, [dir])

    on_exit(fn ->
      if previous,
        do: Process.put(:cure_source_roots, previous),
        else: Process.delete(:cure_source_roots)

      Process.delete(:cure_module_loader_observer)
    end)

    :ok
  end

  test "loading one canonical interface repeatedly is idempotent", %{tmp_dir: dir} do
    provider =
      write!(
        dir,
        "provider.cure",
        """
        mod Merge.Provider
          typealias Code = Int
          fn same(value: Code) -> Code = value
        """
      )

    Process.put(:cure_module_loader_observer, self())

    assert {:ok, env} =
             Program.elaborate("""
             mod Merge.Consumer
               use Merge.Provider
               use Merge.Provider
               fn run(value: Code) -> Code = same(value)
             """)

    assert Map.has_key?(env.defs, :"Merge.Provider#Code")
    assert Map.has_key?(env.defs, :"Merge.Provider#same")

    compiling =
      collect_loader_events()
      |> Enum.filter(&match?({:compiling, "Merge.Provider", ^provider}, &1))

    assert compiling == [{:compiling, "Merge.Provider", provider}]
  end

  test "merge order preserves canonical identities and transparent aliases", %{tmp_dir: dir} do
    write!(
      dir,
      "base.cure",
      """
      mod Merge.Base
        typealias Code = Int
      """
    )

    write!(
      dir,
      "left.cure",
      """
      mod Merge.Left
        use Merge.Base
        fn left(value: Code) -> Code = value
      """
    )

    write!(
      dir,
      "right.cure",
      """
      mod Merge.Right
        use Merge.Base
        fn right(value: Code) -> Code = value
      """
    )

    projections =
      for imports <- [["Merge.Left", "Merge.Right"], ["Merge.Right", "Merge.Left"]] do
        source = """
        mod Merge.Consumer
          use #{Enum.at(imports, 0)}
          use #{Enum.at(imports, 1)}
          fn run(value: Merge.Base.Code) -> Merge.Base.Code = value
        """

        assert {:ok, env} = Program.elaborate(source)

        env.defs
        |> Map.take([
          :"Merge.Base#Code",
          :"Merge.Left#left",
          :"Merge.Right#right",
          :"Merge.Consumer#run"
        ])
      end

    assert [first, second] = projections
    assert first == second
    assert first[:"Merge.Base#Code"].body == {:data, :"Std.Int#Int", [], []}
  end

  test "repeated macro expansion publishes one stable canonical alias" do
    source = """
    mod Merge.GeneratedAlias
      macro Publish
        syntax publish becomes typealias Code = Int

      publish
      fn id(value: Code) -> Code = value
    """

    projections =
      for _round <- 1..3 do
        assert {:ok, env} = Program.elaborate(source)

        alias_keys =
          env.defs
          |> Map.keys()
          |> Enum.filter(&(Cure.Elab.Name.base(&1) == "Code"))

        assert alias_keys == [:"Merge.GeneratedAlias#Code"]

        %{
          alias: env.defs[:"Merge.GeneratedAlias#Code"],
          caller: env.defs[:"Merge.GeneratedAlias#id"],
          bare_bindings: env.bare_bindings
        }
      end

    assert Enum.uniq(projections) |> length() == 1
    assert hd(projections).alias.body == {:data, :"Std.Int#Int", [], []}
  end

  test "indexed aliases remain definitionally identical under every merge order", %{tmp_dir: dir} do
    write!(
      dir,
      "bounded_base.cure",
      """
      mod Merge.BoundedBase
        use Std.Bounded
        typealias Small = Bounded(3)
      """
    )

    for {name, function} <- [{"Left", "left"}, {"Right", "right"}] do
      write!(
        dir,
        "bounded_#{String.downcase(name)}.cure",
        """
        mod Merge.Bounded#{name}
          use Merge.BoundedBase
          fn #{function}(value: Small) -> Small = value
        """
      )
    end

    projections =
      for imports <- [["Merge.BoundedLeft", "Merge.BoundedRight"], ["Merge.BoundedRight", "Merge.BoundedLeft"]] do
        assert {:ok, env} =
                 Program.elaborate("""
                 mod Merge.BoundedConsumer
                   use #{Enum.at(imports, 0)}
                   use #{Enum.at(imports, 1)}
                   fn keep(value: Merge.BoundedBase.Small) -> Merge.BoundedBase.Small = value
                 """)

        %{
          alias: env.defs[:"Merge.BoundedBase#Small"],
          left: env.defs[:"Merge.BoundedLeft#left"],
          right: env.defs[:"Merge.BoundedRight#right"],
          consumer: env.defs[:"Merge.BoundedConsumer#keep"]
        }
      end

    assert [first, second] = projections
    assert first == second
    assert first.alias.body == {:data, :"Std.Bounded#Bounded", [], [nat_lit: 3]}
  end

  test "published interface merges retain the complete coherence universe in every order" do
    assert {:ok, set} = Cure.Compiler.Artifacts.open_verified_set(Cure.Stdlib.Paths.beam_dir())

    interfaces =
      for module <- ["Std.Equatable", "Std.Literal", "Std.String"] do
        path = Cure.Compiler.ModulePipeline.Interface.path(set.artifact_root, module)
        assert {:ok, interface} = Cure.Compiler.ModulePipeline.Interface.read(path)
        interface
      end

    expected_env =
      Enum.reduce(interfaces, Cure.Core.Env.empty(), fn interface, env ->
        assert {:ok, next} = Cure.Compiler.ModulePipeline.Interface.to_env(interface)
        assert {:ok, merged} = Program.merge_canonical_environments(env, next)
        merged
      end)

    for ordered <- [interfaces, Enum.reverse(interfaces)] do
      assert {:ok, merged} = Cure.Compiler.ModulePipeline.Environment.merge(ordered)
      assert merged.env.coherence == expected_env.coherence
    end
  end

  defp collect_loader_events(acc \\ []) do
    receive do
      {:cure_module_loader, event} -> collect_loader_events([event | acc])
    after
      0 -> Enum.reverse(acc)
    end
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
