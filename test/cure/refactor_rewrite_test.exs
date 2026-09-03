defmodule Cure.Refactor.RewriteTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Refactor.Analysis
  alias Cure.Refactor.Rewrite

  setup do
    dir = Path.join(System.tmp_dir!(), "cure_refactor_rewrite_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)

    on_exit(fn -> File.rm_rf!(dir) end)
    {:ok, dir: dir}
  end

  test "split structurally extracts declarations and retains crossing dependency imports", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")

    source = """
    @group(:text)
    mod Source
      use Std.Option

      fn root() -> Int = helper()
      fn helper() -> Int = 1
      fn imported() -> Option(Int) = None()
    end
    """

    File.write!(source_path, source)

    assert {:ok, result} =
             Rewrite.split(source_path, "helpers.cure:Extracted:helper", output_directory: dir)

    assert result.applied? == false
    assert result.source_module == "Source"
    assert result.target_module == "Extracted"
    assert result.selected == ["helper"]
    assert result.added_imports == ["public use Extracted"]
    assert result.source =~ "public use Extracted"
    assert result.source =~ "fn root() -> Int = helper()"
    refute result.source =~ "fn helper() -> Int = 1"
    assert result.target =~ "@group(:text)"
    assert result.target =~ "mod Extracted"
    assert result.target =~ "use Std.Option"
    assert result.target =~ "fn helper() -> Int = 1"

    assert {:ok, source_tokens} = Lexer.tokenize(result.source, file: "source.cure", emit_events: false)
    assert {:ok, _source_ast} = Parser.parse(source_tokens, file: "source.cure", emit_events: false)
    assert {:ok, target_tokens} = Lexer.tokenize(result.target, file: "helpers.cure", emit_events: false)
    assert {:ok, _target_ast} = Parser.parse(target_tokens, file: "helpers.cure", emit_events: false)
    refute File.exists?(Path.join(dir, "helpers.cure"))
  end

  test "apply writes only the verified generated pair", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")
    target_path = Path.join(dir, "helpers.cure")
    File.write!(source_path, "mod Source\n  fn keep() -> Int = 2\n  fn move() -> Int = 1\nend\n")

    assert {:ok, result} =
             Rewrite.split(source_path, %{target_file: "helpers.cure", target_module: "Extracted", selectors: ["move"]},
               output_directory: dir,
               write: true
             )

    assert result.applied?
    assert File.read!(source_path) == result.source
    assert File.read!(target_path) == result.target
    assert result.target =~ "fn move() -> Int = 1"
    refute File.read!(source_path) =~ "fn move()"
  end

  test "split specifications require an explicit destination module" do
    assert {:error, {:invalid_split_spec, message}} = Rewrite.parse_spec("helpers.cure:helper")
    assert message =~ "Target.Module"
  end

  test "an existing target is not overwritten unless explicitly allowed", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")
    target_path = Path.join(dir, "helpers.cure")
    File.write!(source_path, "mod Source\n  fn move() -> Int = 1\nend\n")
    File.write!(target_path, "sentinel")

    assert {:error, {:target_exists, ^target_path}} =
             Rewrite.split(source_path, "helpers.cure:Extracted:move", output_directory: dir, write: true)

    assert File.read!(target_path) == "sentinel"
  end

  test "the compatibility re-export is inserted structurally", %{dir: dir} do
    path = Path.join(dir, "source.cure")
    source = "@group(:text)\nmod Source\n  fn value() -> Int = 1\nend\n"
    File.write!(path, source)

    assert {:ok, %{source: rewritten, added?: true}} =
             Rewrite.ensure_public_use(path, "Extracted", write: false)

    assert rewritten =~ "public use Extracted"
    assert rewritten =~ "fn value() -> Int = 1"
    assert File.read!(path) == source
  end

  test "an importer can be redirected to the extracted module structurally", %{dir: dir} do
    path = Path.join(dir, "source.cure")
    source = "mod Source\n  use Existing\n  fn value() -> Int = 1\nend\n"
    File.write!(path, source)

    assert {:ok, %{source: rewritten, added?: true}} = Rewrite.ensure_use(path, "Extracted", write: false)
    assert rewritten =~ "use Existing\n  use Extracted"
    assert File.read!(path) == source
  end

  test "a split that would require a back-edge is rejected before writing", %{dir: dir} do
    path = Path.join(dir, "source.cure")

    File.write!(path, """
    mod Source
      fn root() -> Int = helper()
      fn helper() -> Int = 1
    end
    """)

    assert {:error, {:dependency_error, message}} =
             Rewrite.split(path, "helpers.cure:Extracted:root", output_directory: dir, write: true)

    assert message =~ "dependency closure"
    refute File.exists?(Path.join(dir, "helpers.cure"))
    assert File.read!(path) =~ "fn root()"
  end

  test "declaration spans include every expression in a multiline body", %{dir: dir} do
    path = Path.join(dir, "multiline.cure")

    File.write!(path, """
    mod Multiline
      fn choose(x: Bool) -> Int =
        pickup
          x -> 1
          else -> 2
        match x
          true -> 1
          false -> 2
    end
    """)

    assert {:ok, report} = Analysis.analyze(path, dependencies: true)
    declaration = Enum.find(report.declarations, &(&1.name == "choose"))
    assert declaration.span.start_line == 2
    assert declaration.span.end_line >= 8
  end
end
