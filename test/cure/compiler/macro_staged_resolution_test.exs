defmodule Cure.Compiler.MacroStagedResolutionTest do
  use ExUnit.Case, async: false

  test "a staged callback uses a local helper over an imported helper" do
    source = """
    mod StagedResolution
      use Std.Syntax
      use Std.List

      macro Probe
        syntax probe <value: Code> computed by derive_probe

      fn map(values: List(t), f: t -> u) -> List(u) = []

      fn derive_probe(input: ProbeSyntax) -> Syntax =
        match map([1, 2], fn(x) -> x)
          [] -> integer(0)
          _ -> integer(1)

      fn answer() -> Int = probe 0
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :answer, []) == 0
  after
    purge(:StagedResolution)
  end

  test "a staged callback resolves a transitive import without a bare global" do
    source = """
    mod StagedTransitiveResolution
      use Std.Syntax

      macro Probe
        syntax probe computed by derive_probe

      fn derive_probe(input: ProbeSyntax) -> Syntax =
        Std.Syntax.leaf(:literal, [attr_value(:subtype, syntax_atom(:string))], syntax_string("7"))

      fn answer() -> String = probe
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    # `String` is a nominal record now, not a `List(Char)` alias, so it erases to
    # `{:String, charlist}` rather than to the bare charlist.
    assert apply(module, :answer, []) == {:String, ~c"7"}
  after
    purge(:StagedTransitiveResolution)
  end

  test "ambiguous imported names remain an error in staged compilation" do
    # `Std.List` and `Std.String` both export `length`, so the bare spelling has
    # two providers and no local winner. An *applied* `length("hello")` is no
    # longer ambiguous — `String` is a nominal record rather than a `List(Char)`
    # alias, so pruning the overload set by argument type leaves exactly one
    # candidate. Referenced as a value there are no argument types to prune with,
    # which is what leaves the guard reachable and what this test pins: staging
    # must not paper over an unresolvable name.
    source = """
    mod StagedAmbiguousResolution
      use Std.{List, String}
      fn measure() -> (String -> Int) = length
    """

    assert {:error, reason} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert {:codegen_error, {:ambiguous_name, :length, providers}} =
             Cure.Elab.Program.semantic_error(reason)

    assert Enum.sort(providers) == ["Std.List", "Std.String"]
  after
    purge(:StagedAmbiguousResolution)
  end

  test "a recursively expanded lifted module resolves a derived BeamEncode dictionary" do
    source = """
    mod StagedBeamDictionary
      use Std.Syntax
      use Std.Beam

      type ChildIdentity = Worker | OtherWorker deriving BeamEncode

      macro Boundary
        syntax boundary <name: ModuleName> becomes lift module name
          use Std.Beam
          behaviour gen_server
          fn encode(id: ChildIdentity) -> BeamTerm = to_beam(id)
          fn encoded() -> BeamTerm = encode(Worker())

      boundary Cure.Generated.StagedBeamBoundary
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert module == :"Cure.StagedBeamDictionary"
    assert apply(:"Cure.Generated.StagedBeamBoundary", :encoded, []) == :Worker
  after
    purge(:StagedBeamDictionary)
    :code.purge(:"Cure.Generated.StagedBeamBoundary")
    :code.delete(:"Cure.Generated.StagedBeamBoundary")
  end

  defp purge(name) do
    module = Module.concat(Cure, name)
    :code.purge(module)
    :code.delete(module)
  end
end
