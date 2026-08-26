defmodule Cure.Elab.ModuleVisibilityTest do
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
    end)

    :ok
  end

  test "a qualified call loads its canonical module without opening its bare name", %{tmp_dir: dir} do
    write!(
      dir,
      "provider.cure",
      """
      mod Canon.Provider
        fn same(n: Int) -> Int = n
      """
    )

    source = """
    mod Canon.Consumer
      fn run(n: Int) -> Int = Canon.Provider.same(n)
    """

    assert {:ok, env} = Program.elaborate(source)

    assert env.defs[:"Canon.Consumer#run"].body == {:global, :"Canon.Provider#same"} or
             contains_global?(env.defs[:"Canon.Consumer#run"].body, :"Canon.Provider#same")

    assert MapSet.member?(env.qualified_modules, "Canon.Provider")
    refute MapSet.member?(env.bare_modules, "Canon.Provider")
  end

  test "a transitive dependency does not leak a bare function", %{tmp_dir: dir} do
    write!(
      dir,
      "provider.cure",
      """
      mod Canon.Provider
        fn hidden(n: Int) -> Int = n
      """
    )

    write!(
      dir,
      "middle.cure",
      """
      mod Canon.Middle
        use Canon.Provider
        fn visible(n: Int) -> Int = hidden(n)
      """
    )

    source = """
    mod Canon.Consumer
      use Canon.Middle
      fn run(n: Int) -> Int = hidden(n)
    """

    assert {:error, reason} = Program.elaborate(source)
    assert inspect(Program.semantic_error(reason)) =~ "unknown"
  end

  test "a computed macro's generated qualified call resolves through the canonical module universe", %{tmp_dir: dir} do
    write!(
      dir,
      "provider.cure",
      """
      mod Canon.Provider
        fn same(n: Int) -> Int = n
      """
    )

    source = """
    mod Canon.Consumer
      use Std.Syntax

      macro Probe
        syntax probe <value: Code> computed by build_probe

      fn build_probe(input: ProbeSyntax) -> Syntax =
        call("Canon.Provider.same", [input.value])

      fn run(n: Int) -> Int = probe n
    """

    assert {:ok, graph} =
             Cure.Compiler.DepGraph.scan(
               [Path.join(dir, "provider.cure"), write!(dir, "consumer.cure", source)],
               validate_dependencies: true
             )

    previous_index = Process.get(:cure_module_index)
    Process.put(:cure_module_index, graph.module_index)

    try do
      assert {:ok, env} = Program.elaborate(source)
      assert contains_global?(env.defs[:"Canon.Consumer#run"].body, :"Canon.Provider#same")
    after
      if previous_index,
        do: Process.put(:cure_module_index, previous_index),
        else: Process.delete(:cure_module_index)
    end
  end

  defp contains_global?({:global, expected}, expected), do: true

  defp contains_global?(term, expected) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&contains_global?(&1, expected))

  defp contains_global?(term, expected) when is_list(term),
    do: Enum.any?(term, &contains_global?(&1, expected))

  defp contains_global?(_term, _expected), do: false

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
