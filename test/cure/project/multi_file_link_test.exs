defmodule Cure.Project.MultiFileLinkTest do
  use ExUnit.Case, async: false

  @moduletag :tmp_dir

  # aa_user.cure sorts alphabetically BEFORE zz_lib.cure, so today's
  # Enum.sort() order compiles the dependent first, and since compiled
  # beams are never loaded between files, codegen's resolve_import finds
  # nothing and silently emits a LOCAL call (codegen.ex:1208-1213).
  # After DepGraph ordering + load-after-compile, the beam import table
  # must carry the remote call.
  test "user->user use + unqualified call produces a remote call regardless of filename order",
       %{tmp_dir: dir} do
    src = Path.join(dir, "src")
    out = Path.join(dir, "ebin")
    File.mkdir_p!(src)

    File.write!(Path.join(src, "aa_user.cure"), """
    mod LinkUser
      use LinkLib
      fn start() -> Int = ping()
    """)

    File.write!(Path.join(src, "zz_lib.cure"), """
    mod LinkLib
      fn ping() -> Int = 41
    """)

    File.write!(Path.join(dir, "Cure.toml"), """
    [project]
    name = "linktest"
    version = "0.1.0"
    source_paths = ["src"]
    """)

    {:ok, project} = Cure.Project.load(dir)

    assert {:ok, %{modules: modules}} =
             Cure.Project.compile_project(project, output_dir: out, check_types: false)

    assert :"Cure.LinkUser" in modules and :"Cure.LinkLib" in modules

    beam =
      out
      |> Cure.Compiler.Artifacts.Writer.resolve()
      |> Path.join("Cure.LinkUser.beam")

    {:ok, {_, [{:imports, imports}]}} = :beam_lib.chunks(String.to_charlist(beam), [:imports])

    assert {:"Cure.LinkLib", :ping, 0} in imports,
           "expected remote call Cure.LinkLib.ping/0 in beam import table, got: #{inspect(imports)}"
  end
end
