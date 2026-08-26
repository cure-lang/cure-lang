defmodule Cure.Compiler.UnresolvedImportWarningTest do
  use ExUnit.Case, async: false

  @moduletag :tmp_dir

  test "imported-but-unresolvable unqualified call is rejected by dependent elaboration",
       %{tmp_dir: dir} do
    # `use Ghost` imports a module that exports no `phantom/0`. The old classic
    # pipeline fell back to a local call and emitted W088; the dependent-only
    # compiler rejects the unknown global before BEAM emission instead.
    ghost = Path.join(dir, "ghost.cure")
    File.write!(ghost, "mod Ghost\n  fn real() -> Int = 1\n")

    user = Path.join(dir, "user.cure")

    File.write!(user, """
    mod GhostUser
      use Ghost
      fn start() -> Int = phantom()
    """)

    out = Path.join(dir, "ebin")

    assert {:ok, %{errors: []}} =
             Cure.Compiler.compile_files([ghost], output_dir: out, emit_events: false)

    # `phantom` is neither a local function of GhostUser nor an export of
    # Ghost, so dependent elaboration rejects the unresolved global before
    # code generation.
    assert {:error, error} =
             Cure.Compiler.compile_file(user,
               output_dir: out,
               emit_events: false,
               check_types: false
             )

    assert {:codegen_error, {:unknown_global, :phantom, _detail}} =
             Cure.Elab.Program.semantic_error(error)
  end
end
