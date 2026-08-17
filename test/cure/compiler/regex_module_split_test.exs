defmodule Cure.Compiler.RegexModuleSplitTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.ModuleManifest
  alias Cure.Compiler.ModuleIndex
  alias Cure.Elab.Program
  alias Cure.Compiler.ModulePipeline
  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.Name

  @moduletag :tmp_dir

  test "the public façade re-exports Core and Runtime through classic elaboration" do
    source = """
    mod RegexFacadeSurface
      use Std.Regex

      fn build() -> Pattern(CharC) = PatternPredicate(fn(_) -> true)
    end
    """

    assert {:ok, _env} = Program.elaborate(source, file: "regex_facade_surface.cure")
  end

  test "the Regex layers have one-way manifest ownership" do
    paths =
      [
        "lib/std/regex_core.cure",
        "lib/std/regex_runtime.cure",
        "lib/std/regex_proof.cure",
        "lib/std/regex.cure",
        "lib/std/regex_language.cure"
      ]
      |> Enum.map(&Path.expand/1)

    assert {:ok, stdlib_index} =
             ModuleIndex.build(Path.wildcard("lib/std/**/*.cure"), validate_dependencies: false)

    assert {:ok, manifest} =
             ModuleManifest.build(paths,
               package: "stdlib",
               known_modules: ["Std.Builtin" | ModuleIndex.module_names(stdlib_index)]
             )

    dependencies = fn module_name ->
      manifest
      |> ModuleManifest.dependencies(module_name)
      |> Enum.map(&elem(&1.target, 1))
      |> MapSet.new()
    end

    assert "Std.Regex.Core" in dependencies.("Std.Regex.Runtime")
    assert "Std.Regex.Runtime" in dependencies.("Std.Regex.Proof")
    assert "Std.Regex.Proof" in dependencies.("Std.Regex")
    assert "Std.Regex.Core" in dependencies.("Std.Regex.Language")
    assert "Std.Regex.Runtime" in dependencies.("Std.Regex.Language")
    assert "Std.Regex.Proof" in dependencies.("Std.Regex.Language")

    refute "Std.Regex.Proof" in dependencies.("Std.Regex.Core")
    refute "Std.Regex" in dependencies.("Std.Regex.Core")
    refute "Std.Regex" in dependencies.("Std.Regex.Proof")
  end

  test "canonical visibility follows transitive public reexports", %{tmp_dir: dir} do
    base = Path.join(dir, "base.cure")
    middle = Path.join(dir, "middle.cure")
    facade = Path.join(dir, "facade.cure")

    File.write!(base, "mod Surface.Base\n  fn value() -> Int = 41\n")

    File.write!(
      middle,
      "mod Surface.Middle\n  public use Surface.Base\n"
    )

    File.write!(
      facade,
      "mod Surface.Facade\n  public use Surface.Middle\n  fn result() -> Int = value() + 1\n"
    )

    assert {:ok, _result} =
             ModulePipeline.check([facade, middle, base],
               module_pipeline: :canonical,
               package: "surface",
               source_roots: [dir]
             )
  end

  test "canonical qualified compatibility roots preserve public reexports", %{tmp_dir: dir} do
    base = Path.join(dir, "base.cure")
    facade = Path.join(dir, "facade.cure")
    consumer = Path.join(dir, "consumer.cure")

    File.write!(base, "mod Surface.Base\n  fn value() -> Int = 41\n")
    File.write!(facade, "mod Surface.Facade\n  public use Surface.Base\n")

    File.write!(
      consumer,
      "mod Surface.Consumer\n  use Surface.Facade\n  fn result() -> Int = Surface.Facade.value()\n"
    )

    assert {:ok, _result} =
             ModulePipeline.check([consumer, facade, base],
               module_pipeline: :canonical,
               package: "surface",
               source_roots: [dir]
             )
  end

  test "the compatibility inventory resolves to one canonical owner" do
    source = """
    mod RegexFacadeInventory
      use Std.Regex
      fn keep({shape: ShapeCode}, value: Pattern(shape)) -> Pattern(shape) = value
    end
    """

    assert {:ok, env} = Program.elaborate(source, file: "regex_facade_inventory.cure")

    # This is the reviewed public inventory for the façade. The test deliberately
    # checks canonical environment entries rather than merely parsing names from
    # the source file, so copying a second nominal family cannot pass unnoticed.
    public_families = [
      {:Pattern, 1},
      {:ShapeCode, 0},
      {:EvidenceInstruction, 0},
      {:Evidence, 0},
      {:Encodes, 3},
      {:EncodesMany, 3},
      {:EncodingExtraction, 3},
      {:ManyEncodingExtraction, 3},
      {:ThreadState, 1},
      {:MachineState, 1},
      {:PatternMachine, 1}
    ]

    Enum.each(public_families, fn {name, _arity} ->
      facade_key = String.to_atom("Std.Regex##{name}")
      core_key = String.to_atom("Std.Regex.Core##{name}")
      assert Inductive.get_family(env, facade_key) == nil
      family = Inductive.get_family(env, core_key)
      assert family.name == core_key
    end)

    public_functions = ~w(parse_pattern_full parse_program_full parse_full parse_prefix search scan split replace)

    Enum.each(public_functions, fn name ->
      key = String.to_atom("Std.Regex##{name}")
      assert %{name: ^key} = Env.get_def(env, key)
      assert Name.owner(key) == "Std.Regex"
    end)

    # Constructors are also part of the inventory and must resolve through the
    # Core owner without leaving a façade-owned duplicate.
    assert Inductive.get_ctor(env, :"Std.Regex#PatternEmpty") == nil
    assert Inductive.get_ctor(env, :"Std.Regex.Core#PatternEmpty").name == :"Std.Regex.Core#PatternEmpty"
    assert Inductive.get_ctor(env, :"Std.Regex#PatternPredicate") == nil
    assert Inductive.get_ctor(env, :"Std.Regex.Core#PatternPredicate").name == :"Std.Regex.Core#PatternPredicate"

    # The inventory above is intentionally readable. This second assertion is
    # exhaustive for all public Core/Runtime families visible through the
    # façade: every base name has one canonical owner and never a façade-owned
    # nominal duplicate.
    canonical_families =
      env.families
      |> Map.keys()
      |> Enum.filter(&(Name.owner(&1) in ["Std.Regex.Core", "Std.Regex.Runtime"]))

    Enum.each(canonical_families, fn key ->
      refute Inductive.get_family(env, String.to_atom("Std.Regex##{Name.base(key)}"))
      assert Name.owner(key) in ["Std.Regex.Core", "Std.Regex.Runtime"]
    end)
  end

  test "qualified façade type families resolve through canonical public reexports" do
    source = """
    mod RegexQualifiedFacadeInventory
      use Std.Regex
      fn keep({shape: Std.Regex.ShapeCode}, value: Std.Regex.Pattern(shape)) -> Std.Regex.Pattern(shape) = value
    end
    """

    assert {:ok, _env} = Program.elaborate(source, file: "regex_qualified_facade_inventory.cure")
  end
end
