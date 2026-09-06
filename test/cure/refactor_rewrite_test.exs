defmodule Cure.Refactor.RewriteTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, ModulePipeline, Parser}
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

  test "split downgrades source re-exports to ordinary target imports", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")

    File.write!(source_path, """
    mod Source
      public use Existing
      fn move() -> Int = external()
    end
    """)

    assert {:ok, result} =
             Rewrite.split(source_path, "helpers.cure:Extracted:move", output_directory: dir)

    assert result.target =~ "use Existing"
    refute result.target =~ "public use Existing"
  end

  test "split preserves reducibility for definitions used in dependent source types", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")

    File.write!(source_path, """
    mod Source
      type Vec(a: Type) indices (n: Nat)
        empty : Vec(a, Z)

      fn index() -> Nat = Z()
      fn result() -> Vec(Int, index()) = empty()
    end
    """)

    assert {:ok, result} =
             Rewrite.split(source_path, "index.cure:Extracted:index",
               output_directory: dir,
               write: true
             )

    assert result.target =~ "  @reducible\n  fn index()"

    assert {:ok, _pipeline} =
             ModulePipeline.check(
               [source_path, Path.join(dir, "index.cure")],
               module_pipeline: :canonical,
               package: "dependent_split",
               source_roots: [dir]
             )
  end

  test "split_fragments preserves one canonical module identity across dependent groups", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")

    File.write!(source_path, """
    mod Source
      fn first() -> Int = 1
      fn second() -> Int = first()
      fn third() -> Int = second()
    end
    """)

    assert {:ok, result} =
             Rewrite.split_fragments(
               source_path,
               [
                 "first.cure:Source:first",
                 "second.cure:Source:second"
               ],
               output_directory: dir,
               write: true
             )

    assert result.source =~ "# cure:fragment"
    assert Enum.all?(result.targets, &(&1.target =~ "# cure:fragment"))
    assert Enum.all?(result.targets, &(&1.target =~ "mod Source"))
    assert File.read!(Path.join(dir, "first.cure")) =~ "fn first() -> Int = 1"
    assert File.read!(Path.join(dir, "second.cure")) =~ "fn second() -> Int = first()"
    refute result.source =~ "fn first() -> Int = 1"
    refute result.source =~ "fn second() -> Int = first()"
  end

  test "dependency analysis records references from type-alias bodies", %{dir: dir} do
    path = Path.join(dir, "aliases.cure")

    File.write!(path, """
    mod Aliases
      type Inner = Nat
      typealias Wrapped = List(Inner)
      type Box = WrappedBox(Inner)
    end
    """)

    assert {:ok, report} = Analysis.analyze(path, dependencies: true)
    alias_declaration = Enum.find(report.declarations, &(&1.name == "Wrapped"))

    assert Enum.any?(alias_declaration.references, fn reference ->
             reference.identity == :"Aliases#Inner" and reference.kind == :type
           end)

    enum_declaration = Enum.find(report.declarations, &(&1.name == "Box"))

    assert Enum.any?(enum_declaration.references, fn reference ->
             reference.identity == :"Aliases#Inner" and reference.kind == :type
           end)
  end

  test "split updates direct importers of moved declarations", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")
    importer_path = Path.join(dir, "consumer.cure")

    File.write!(source_path, """
    mod Source
      fn root() -> Int = helper()
      fn helper() -> Int = 1
    end
    """)

    File.write!(importer_path, """
    mod Consumer
      use Source
      fn result() -> Int = helper()
    end
    """)

    assert {:ok, result} =
             Rewrite.split(source_path, "helpers.cure:Extracted:helper",
               output_directory: dir,
               write: true
             )

    assert result.updated_dependents == [importer_path]
    assert File.read!(importer_path) =~ "use Extracted"
    assert File.read!(source_path) =~ "public use Extracted"
    assert File.read!(Path.join(dir, "helpers.cure")) =~ "fn helper() -> Int = 1"
  end

  test "split updates importers that use moved type constructors in signatures", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")
    importer_path = Path.join(dir, "consumer.cure")

    File.write!(source_path, """
    mod Source
      type Nat = Z | S(Nat)
      fn root() -> Int = 1
    end
    """)

    File.write!(importer_path, """
    mod Consumer
      use Source
      fn successor(value: Nat) -> Nat = S(value)
    end
    """)

    assert {:ok, result} =
             Rewrite.split(source_path, "types.cure:Extracted:Nat",
               output_directory: dir,
               write: true
             )

    assert result.updated_dependents == [importer_path]
    assert File.read!(importer_path) =~ "use Extracted"
    assert File.read!(source_path) =~ "public use Extracted"
    assert File.read!(Path.join(dir, "types.cure")) =~ "type Nat = Z | S(Nat)"
  end

  test "split updates importers that alias a moved type", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")
    importer_path = Path.join(dir, "consumer.cure")

    File.write!(source_path, """
    mod Source
      type Nat = Z | S(Nat)
    end
    """)

    File.write!(importer_path, """
    mod Consumer
      use Source
      type Alias = Nat
    end
    """)

    assert {:ok, result} =
             Rewrite.split(source_path, "types.cure:Extracted:Nat",
               output_directory: dir,
               write: true
             )

    assert result.updated_dependents == [importer_path]
    assert File.read!(importer_path) =~ "use Extracted"
  end

  test "split preserves implicit list inference through a public type re-export", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")

    File.write!(source_path, """
    mod Source
      type Modifier = Caseless | Multiline
      type Policy = LF | Unicode
      type Options = Options(List(Modifier), Policy)

      fn defaults() -> Options = Options([], Unicode)
    end
    """)

    assert {:ok, result} =
             Rewrite.split(source_path, "atoms.cure:Atoms:Modifier|Policy",
               output_directory: dir
             )

    target_path = Path.join(dir, "atoms.cure")
    File.write!(target_path, result.target)

    utility_path = Path.join(dir, "utility.cure")

    File.write!(utility_path, """
    mod Utility
      use Source
      fn defaults() -> Options = Options([], Unicode)
    end
    """)

    assert {:ok, _pipeline} =
             ModulePipeline.check([utility_path, source_path, target_path],
               module_pipeline: :canonical,
               package: "reexport",
               source_roots: [dir]
             )

    assert result.target =~ "type Modifier = Caseless | Multiline"
    assert result.target =~ "type Policy = LF | Unicode"
    assert result.source =~ "public use Atoms"
    assert result.source =~ "Options([], Unicode)"
  end

  test "split keeps a moved map distinct from Std.List.map", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")
    consumer_path = Path.join(dir, "consumer.cure")

    File.write!(source_path, """
    mod Source
      fn map(left: Int, right: Int) -> Int = left
    end
    """)

    File.write!(consumer_path, """
    mod Consumer
      use Source
      use Std.List
      fn result() -> Int = map(1, 2)
    end
    """)

    assert {:ok, result} =
             Rewrite.split(source_path, "map.cure:Extracted:map",
               output_directory: dir,
               write: true
             )

    assert result.updated_dependents == [consumer_path]
    assert File.read!(consumer_path) =~ "use Extracted"

    assert File.read!(source_path) =~ "public use Extracted"
  end

  test "leading documentation trivia follows an extracted declaration", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")

    source = """
    mod Source
      ## Documentation for the moved declaration.
      @reducible
      fn move() -> Int = 1
      fn keep() -> Int = 2
    end
    """

    File.write!(source_path, source)

    assert {:ok, result} =
             Rewrite.split(source_path, "helpers.cure:Extracted:move", output_directory: dir)

    assert result.target =~ "## Documentation for the moved declaration."
    assert result.target =~ "@reducible"
    assert result.target =~ "  @reducible\n  fn move()"
    refute result.source =~ "Documentation for the moved declaration"
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

  test "split moves a closed private helper with its public caller", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")

    File.write!(source_path, """
    mod Source
      fn root(value: Int) -> Int = helper(value)
      local fn helper(value: Int) -> Int = value
    end
    """)

    assert {:ok, result} =
             Rewrite.split(source_path, "helpers.cure:Extracted:root|helper",
               output_directory: dir
             )

    assert result.target =~ "fn root(value: Int) -> Int = helper(value)"
    assert result.target =~ "local fn helper(value: Int) -> Int = value"
    assert result.source =~ "public use Extracted"
    refute result.source =~ "fn root(value: Int)"
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
    assert rewritten =~ "use Existing"
    assert rewritten =~ "use Extracted"
    assert File.read!(path) == source
  end

  test "an ordinary use can be added alongside an existing public re-export", %{dir: dir} do
    path = Path.join(dir, "source.cure")
    source = "mod Source\n  public use Extracted\n  fn value() -> Int = 1\nend\n"
    File.write!(path, source)

    assert {:ok, %{source: rewritten, added?: true}} = Rewrite.ensure_use(path, "Extracted", write: false)
    assert rewritten =~ "use Extracted"
    assert rewritten =~ "public use Extracted"
    assert File.read!(path) == source
  end

  test "reducibility annotations are added to selected declarations structurally", %{dir: dir} do
    path = Path.join(dir, "source.cure")
    source = "mod Source\n  ## Keep this documentation attached.\n  fn value() -> Int = 1\nend\n"
    File.write!(path, source)

    assert {:ok, %{source: rewritten, added: ["value"]}} =
             Rewrite.ensure_reducible(path, ["value"], write: false)

    assert rewritten =~ "## Keep this documentation attached.\n  @reducible\n  fn value()"
    assert File.read!(path) == source
  end

  test "an ordinary import can be removed structurally", %{dir: dir} do
    path = Path.join(dir, "source.cure")
    source = "mod Source\n  use Existing\n  use Extracted\n  fn value() -> Int = 1\nend\n"
    File.write!(path, source)

    assert {:ok, %{source: rewritten, removed?: true}} = Rewrite.remove_use(path, "Extracted")
    assert rewritten =~ "use Existing"
    refute rewritten =~ "use Extracted"
    assert rewritten =~ "fn value() -> Int = 1"
    assert File.read!(path) == source
  end

  test "ordinary imports can be pruned structurally while public uses survive", %{dir: dir} do
    path = Path.join(dir, "source.cure")

    source =
      "mod Source\n  use Keep\n  use Remove\n  public use Public\n  fn value() -> Int = 1\nend\n"

    File.write!(path, source)

    assert {:ok, %{source: rewritten, removed: ["Remove"]}} = Rewrite.prune_uses(path, ["Keep"])
    assert rewritten =~ "use Keep"
    refute rewritten =~ "use Remove"
    assert rewritten =~ "public use Public"
    assert File.read!(path) == source
  end

  test "trailing newline normalization is verified before writing", %{dir: dir} do
    path = Path.join(dir, "source.cure")
    source = "mod Source\n  fn value() -> Int = 1\nend\n\n"
    File.write!(path, source)

    assert {:ok, %{source: rewritten, changed?: true}} = Rewrite.normalize_trailing_newline(path, write: true)
    assert rewritten == "mod Source\n  fn value() -> Int = 1\nend\n"
    assert File.read!(path) == rewritten
  end

  test "decorated declarations can be re-anchored after an older split", %{dir: dir} do
    path = Path.join(dir, "malformed.cure")

    File.write!(path, "mod Source\n  @reducible\n    fn value() -> Int = 1\nend\n")

    assert {:ok, %{source: rewritten, changed?: true}} =
             Rewrite.normalize_module_indentation(path)

    assert rewritten =~ "  @reducible\n  fn value()"
    refute rewritten =~ "  @reducible\n    fn value()"
    assert File.read!(path) == "mod Source\n  @reducible\n    fn value() -> Int = 1\nend\n"
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

  test "prelude constructors do not look like source-side split dependencies", %{dir: dir} do
    path = Path.join(dir, "source.cure")

    File.write!(path, """
    mod Source
      fn bound() -> Nat = S(S(Z()))
      fn keep() -> Int = 1
    end
    """)

    assert {:ok, result} =
             Rewrite.split(path, "limits.cure:Extracted:bound", output_directory: dir)

    assert result.selected == ["bound"]
    assert result.added_imports == ["public use Extracted"]
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

  test "split_many extracts independent closed groups in one source rewrite", %{dir: dir} do
    source_path = Path.join(dir, "source.cure")

    File.write!(source_path, """
    mod Source
      fn first() -> Int = 1
      fn second() -> Int = 2
      fn keep() -> Int = first() + second()
    end
    """)

    assert {:ok, result} =
             Rewrite.split_many(
               source_path,
               [
                 %{target_file: "first.cure", target_module: "Extracted.First", selectors: ["first"]},
                 %{target_file: "second.cure", target_module: "Extracted.Second", selectors: ["second"]}
               ],
               output_directory: dir
             )

    assert result.applied? == false
    assert result.source =~ "public use Extracted.First"
    assert result.source =~ "public use Extracted.Second"
    refute result.source =~ "fn first()"
    refute result.source =~ "fn second()"
    assert Enum.map(result.targets, & &1.target_module) == ["Extracted.First", "Extracted.Second"]
    assert Enum.at(result.targets, 0).target =~ "fn first() -> Int = 1"
    assert Enum.at(result.targets, 1).target =~ "fn second() -> Int = 2"
  end
end
