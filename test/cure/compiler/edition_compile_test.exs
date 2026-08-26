# F-A (audit iteration 3): the compile pipeline (Cure.Compiler) must resolve each
# source's edition (file @edition pragma > Cure.toml [project].edition > default)
# and drive the lexer/parser with it — spec §3.2/§4. Before this wiring the build
# path was edition-blind: it always lexed under current() and never consulted
# resolve/1, so a typo'd edition compiled silently (§3.1 violation) and §4's
# edition-parameterized lexing was dead on the build path.
defmodule Cure.Compiler.EditionCompileTest do
  use ExUnit.Case, async: true

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_edcompile_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "compile fails loudly on an unknown @edition pragma (resolve gate, before codegen)" do
    src = "@edition(\"9999\")\nmod M\n  fn f() -> Int = 1\n"

    assert {:error, {:edition_error, {:unknown_edition, "9999"}}} =
             Cure.Compiler.compile_string(src, file: "t.cure", emit_events: false)
  end

  test "compile fails loudly when the project manifest declares an unknown edition", %{dir: dir} do
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"1999\"\n")
    src = "mod M\n  fn f() -> Int = 1\n"

    assert {:error, {:edition_error, {:unknown_edition, "1999"}}} =
             Cure.Compiler.compile_string(src,
               file: "t.cure",
               emit_events: false,
               project_dir: dir
             )
  end

  # Iteration 8 (audit F1): parse_source is the headless tooling entry (dep_graph,
  # formatters). Once it discovers project_dir from the real :file, resolve/1 can
  # return {:error, {:unknown_edition, _}} from a typo'd MANIFEST for a pragma-less
  # source — which the parser CANNOT re-catch (the manifest isn't in the source).
  # Swallowing it to current() silently degraded a real edition error; surface it
  # like the compile path.
  test "parse_source surfaces an unknown manifest edition instead of degrading to default",
       %{dir: dir} do
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"1999\"\n")
    file = Path.join(dir, "m.cure")
    src = "mod M\n  fn f() -> Int = 1\n"
    File.write!(file, src)

    assert {:error, {:edition_error, {:unknown_edition, "1999"}}} =
             Cure.Compiler.parse_source(src, file: file)
  end

  test "parse_source parses normally under a valid manifest edition", %{dir: dir} do
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"2026\"\n")
    file = Path.join(dir, "m.cure")
    src = "mod M\n  fn f() -> Int = 1\n"
    File.write!(file, src)

    assert {:ok, _ast} = Cure.Compiler.parse_source(src, file: file)
  end

  test "compile honors a valid manifest edition (resolve is consulted, no crash)", %{dir: dir} do
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"2026\"\n")
    src = "mod M\n  fn f() -> Int = 1\n"

    assert {:ok, _mod, _warns} =
             Cure.Compiler.compile_string(src,
               file: "t.cure",
               emit_events: false,
               project_dir: dir,
               output_dir: dir
             )
  end

  test "compile with a valid @edition pragma still compiles", %{dir: dir} do
    src = "@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n"

    assert {:ok, _mod, _warns} =
             Cure.Compiler.compile_string(src, file: "t.cure", emit_events: false, output_dir: dir)
  end

  # Iteration 5 (F-A follow-up): compile_file must resolve each file under its
  # NEAREST ANCESTOR Cure.toml (spec §3.2: pragma > Cure.toml > default), not only
  # when a caller explicitly passes :project_dir. The CLI build/run callers never
  # thread :project_dir, so before this a project's [project].edition — including
  # a TYPO'd one — was silently ignored on the build path (§3.1 "fail loudly"
  # violated). Auto-discovery walks up from the file's own directory.
  test "compile_file fails loudly on an unknown edition in an ancestor Cure.toml", %{dir: dir} do
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"9999\"\n")
    file = Path.join(dir, "a.cure")
    File.write!(file, "mod M\n  fn f() -> Int = 1\n")

    assert {:error, {:edition_error, {:unknown_edition, "9999"}}} =
             Cure.Compiler.compile_file(file, emit_events: false, output_dir: dir)
  end

  test "compile_file resolves the NEAREST ancestor Cure.toml (child shadows parent)", %{dir: dir} do
    # Parent manifest is valid; the nearer child manifest is a typo. Nearest wins,
    # so the build must fail on the child's "9999", proving it is not merely
    # scanning cwd or any ancestor.
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"2026\"\n")
    sub = Path.join(dir, "sub")
    File.mkdir_p!(sub)
    File.write!(Path.join(sub, "Cure.toml"), "[project]\nname = \"y\"\nedition = \"9999\"\n")
    file = Path.join(sub, "a.cure")
    File.write!(file, "mod M\n  fn f() -> Int = 1\n")

    assert {:error, {:edition_error, {:unknown_edition, "9999"}}} =
             Cure.Compiler.compile_file(file, emit_events: false, output_dir: dir)
  end

  test "compile_file honors a valid ancestor Cure.toml across a subdirectory", %{dir: dir} do
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"2026\"\n")
    sub = Path.join(dir, "sub")
    File.mkdir_p!(sub)
    file = Path.join(sub, "a.cure")
    File.write!(file, "mod M\n  fn f() -> Int = 1\n")

    assert {:ok, _mod, _warns} =
             Cure.Compiler.compile_file(file, emit_events: false, output_dir: dir)
  end

  test "a file @edition pragma overrides an unknown ancestor Cure.toml (precedence)", %{dir: dir} do
    # Pragma > Cure.toml: a valid pragma must win over a typo'd manifest, so the
    # file compiles rather than failing on the manifest's bad edition.
    File.write!(Path.join(dir, "Cure.toml"), "[project]\nname = \"x\"\nedition = \"9999\"\n")
    file = Path.join(dir, "a.cure")
    File.write!(file, "@edition(\"2026\")\nmod M\n  fn f() -> Int = 1\n")

    assert {:ok, _mod, _warns} =
             Cure.Compiler.compile_file(file, emit_events: false, output_dir: dir)
  end
end
