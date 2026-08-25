defmodule Cure.Elab.CanonicalModuleLoaderTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  setup do
    root = Path.join(System.tmp_dir!(), "cure_loader_#{System.unique_integer([:positive])}")
    File.mkdir_p!(root)
    previous_roots = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, [root])

    on_exit(fn ->
      if previous_roots,
        do: Process.put(:cure_source_roots, previous_roots),
        else: Process.delete(:cure_source_roots)

      File.rm_rf!(root)
    end)

    {:ok, root: root}
  end

  test "a diamond elaborates its shared interface exactly once", %{root: root} do
    write_module(root, "base.cure", "Loader.Base", "fn value() -> Int = 1")
    write_module(root, "left.cure", "Loader.Left", "use Loader.Base")
    write_module(root, "right.cure", "Loader.Right", "use Loader.Base")
    Process.put(:cure_module_loader_observer, self())

    assert {:ok, _env} =
             Program.elaborate("""
             mod Loader.Main
               use Loader.Left
               use Loader.Right
               fn result() -> Int = Loader.Base.value()
             end
             """)

    events = drain_loader_events([])
    assert Enum.count(events, &match?({:compiling, "Loader.Base", _}, &1)) == 1
  after
    Process.delete(:cure_module_loader_observer)
  end

  # A `use` cycle is not an elaboration error. `load_module_interface/2` answers a
  # back-edge with a types -> signatures -> conformance skeleton, so each member
  # sees its peer's interface and the outer load still checks every body once the
  # complete peer interfaces exist. The stdlib depends on exactly this:
  # `Std.Char` and `Std.String` are mutually recursive by design.
  #
  # Cycles are still reported, once, from the one place that can see the whole
  # file set: `Cure.Compiler.DepGraph`. Every driver (`mix cure.compile`,
  # `Cure.CLI`, `Cure.Project`) renders its walks as the W086 warning.
  test "an import cycle elaborates through canonical interfaces", %{root: root} do
    a =
      write_module(
        root,
        "a.cure",
        "Loader.A",
        "use Loader.B\n  fn from_a() -> Int = 1\n  fn a_uses_b() -> Int = from_b()"
      )

    b =
      write_module(
        root,
        "b.cure",
        "Loader.B",
        "use Loader.A\n  fn from_b() -> Int = 2\n  fn b_uses_a() -> Int = from_a()"
      )

    assert {:ok, env} =
             Program.elaborate("mod Loader.Main\n  use Loader.A\n  fn result() -> Int = a_uses_b()\nend\n")

    # The back-edge resolved to a canonical identity, not to a re-declared local
    # copy: the skeleton published `Loader.A`'s signature, and the body that
    # crosses back into `Loader.B` was checked against `Loader.B`'s own.
    assert %{body: {:global, :"Loader.A#a_uses_b"}} = Map.fetch!(env.defs, :"Loader.Main#result")
    assert %{body: {:global, :"Loader.B#from_b"}} = Map.fetch!(env.defs, :"Loader.A#a_uses_b")
    assert %{body: {:global, :"Loader.A#from_a"}} = Map.fetch!(env.defs, :"Loader.B#b_uses_a")

    # And the cycle is still surfaced, with every hop located so W086 can print
    # the file and line each `use` sits on.
    assert {:ok, _ordered, [walk]} =
             [a, b] |> Cure.Compiler.DepGraph.scan() |> then(fn {:ok, graph} -> Cure.Compiler.DepGraph.order(graph) end)

    assert Enum.map(walk, & &1.module) == ["Loader.A", "Loader.B", "Loader.A"]
    assert Enum.map(walk, & &1.path) == [a, b, a]
    assert Enum.all?(walk, &is_integer(&1.line))
  end

  test "two source files cannot declare one canonical identity", %{root: root} do
    write_module(root, "first.cure", "Loader.Duplicate", "fn first() -> Int = 1")
    write_module(root, "second.cure", "Loader.Duplicate", "fn second() -> Int = 2")

    assert {:error, {:duplicate_module_identity, "Loader.Duplicate", paths}} =
             Program.elaborate("mod Loader.Main\n  use Loader.Duplicate\nend\n")

    assert length(paths) == 2
  end

  test "a new elaboration generation observes changed source", %{root: root} do
    path = write_module(root, "changing.cure", "Loader.Changing", "fn value() -> Int = 1")
    Process.put(:cure_module_loader_observer, self())
    main = "mod Loader.Main\n  use Loader.Changing\n  fn result() -> Int = value()\nend\n"

    assert {:ok, _env} = Program.elaborate(main)
    File.write!(path, "mod Loader.Changing\n  fn value() -> Int = 2\nend\n")
    assert {:ok, _env} = Program.elaborate(main)

    events = drain_loader_events([])
    assert Enum.count(events, &match?({:compiling, "Loader.Changing", _}, &1)) == 2
  after
    Process.delete(:cure_module_loader_observer)
  end

  test "a totality failure in an imported module renders that module's authored definition", %{root: root} do
    path = Path.join(root, "non_total.cure")

    imported = """
    mod Loader.NonTotal
      type Dec = Dcoupled | Causal
      type Sig = CSig | ESig
      type SVDesc = SVNil | SVCons(Sig, SVDesc)
      fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)
      type SF indices (as: SVDesc, bs: SVDesc, d: Dec)
        prim : SF(as, bs, Causal)
        seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))
    end
    """

    File.write!(path, imported)
    main = "mod Loader.Main\n  use Loader.NonTotal\nend\n"

    assert {:error, error} = Program.elaborate(main, file: "main.cure")
    assert {:totality_required, :"Loader.NonTotal#andd"} = Program.semantic_error(error)

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "main.cure", main)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

    assert diagnostic.primary.span.path == path
    assert diagnostic.primary.span.start_line == 5
    assert rendered =~ path
    assert rendered =~ "non_total.cure:5:36"
    assert rendered =~ "5 |   fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)"
    assert rendered =~ "^^^^ this recursive call participates in an unproven termination cycle"
    assert rendered =~ "this type-level function must terminate on every input"
    refute rendered =~ "at main.cure"
  end

  defp write_module(root, file, module_name, body) do
    path = Path.join(root, file)
    File.write!(path, "mod #{module_name}\n  #{body}\nend\n")
    path
  end

  defp drain_loader_events(events) do
    receive do
      {:cure_module_loader, event} -> drain_loader_events([event | events])
    after
      0 -> Enum.reverse(events)
    end
  end
end
