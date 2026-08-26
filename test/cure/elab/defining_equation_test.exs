defmodule Cure.Elab.DefiningEquationTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Env, Kernel, Validator}
  alias Cure.Elab.{Equation, Program}

  @source """
  mod EquationFixture
    type Nat = Z | S(Nat)

    fn identity(n: Nat) -> Nat = match n
      Z -> Z
      S(previous) -> S(previous)

    fn expose_zero_equation() = identity.Z
  end
  """

  setup do
    root = Path.join(System.tmp_dir!(), "cure_equations_#{System.unique_integer([:positive])}")
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

  test "flat decision-tree branches become certified ordinary equality definitions" do
    assert {:ok, env} = Program.elaborate(@source)
    equations = Env.equations(env, :identity)

    assert Enum.map(equations, & &1.pattern_key) == ["identity/Z", "identity/S"]

    assert Enum.map(equations, &Enum.map(&1.constructor_path, fn name -> Cure.Elab.Name.base(name) end)) == [
             ["Z"],
             ["S"]
           ]

    for equation <- equations do
      metadata = Equation.source_metadata(equation)

      assert equation.owner == :"EquationFixture#identity"
      assert metadata.definition_span
      assert metadata.left_surface && metadata.right_surface
      assert equation.left_core && equation.right_core
      assert equation.visibility == :public
      assert metadata.provenance.kind == :generated_defining_equation
      assert Env.certified?(env, equation.theorem)
      assert :ok = Kernel.check_def(env, equation.theorem)

      definition = Env.get_def(env, equation.theorem)
      assert definition.generated_equation
      refute Enum.any?(Validator.nodes(definition.body), &match?({:rewrite_command, _, _}, &1))
    end

    zero = Enum.find(equations, &(&1.pattern_key == "identity/Z"))
    zero_metadata = Equation.source_metadata(zero)
    assert {:function_call, [name: "identity"], [{:variable, _, "Z"}]} = zero_metadata.left_surface
    assert {:variable, _, "Z"} = zero_metadata.right_surface
    assert zero_metadata.definition_span.start_line == 5
  end

  test "friendly constructor members resolve without traversal ordinals" do
    assert {:ok, env} = Program.elaborate(@source)
    assert %{generated_equation: true} = Env.get_def(env, :"identity$equation$Z")
    assert %{generated_equation: true} = Env.get_def(env, :"identity$equation$S")
    refute Enum.any?(Map.keys(env.defs), &(Atom.to_string(&1) =~ ~r/identity\.eq_[0-9]+/))

    assert %{body: {:global, :"EquationFixture#identity$equation$Z"}} = Env.get_def(env, :expose_zero_equation)
  end

  test "generated defining equations can be applied at the authored friendly name" do
    source = """
    mod AppliedEquation
      use Std.Equivalent
      type Nat3 = Z3 | S3(Nat3)
      fn add3(x: Nat3, y: Nat3) -> Nat3 = match x
        Z3() -> y
        S3(k) -> S3(add3(k, y))
      fn add3_succ_eq(k: Nat3, y: Nat3) -> Equivalent(Nat3, add3(S3(k), y), S3(add3(k, y))) =
        add3.S3(k, y)
    end
    """

    assert {:ok, env} = Program.elaborate(source)

    definition = Env.get_def(env, :add3_succ_eq)

    assert Enum.any?(Validator.nodes(definition.body), fn
             {:global, theorem} -> Atom.to_string(theorem) =~ "add3$equation$S3"
             _ -> false
           end)

    assert {:ok, _module} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "equation metadata and theorem identities survive deterministic recompilation" do
    assert {:ok, first} = Program.elaborate(@source)
    assert {:ok, second} = Program.elaborate(@source)

    project = fn env ->
      Env.equations(env, :identity)
      |> Enum.map(&Map.take(&1, [:theorem, :constructor_path, :pattern_key, :left_core, :right_core]))
    end

    assert project.(first) == project.(second)
  end

  test "nested matches use complete constructor paths and ambiguous short members do not resolve" do
    source = """
    mod NestedEquations
      type Bit = Off | On

      fn both(left: Bit, right: Bit) -> Bit = match left
        Off -> Off
        On -> match right
          Off -> Off
          On -> On
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    equations = Env.equations(env, :both)
    assert Enum.map(equations, & &1.pattern_key) == ["both/Off", "both/On/Off", "both/On/On"]

    assert {:error, {:defining_equation_unavailable, :friendly_name_collision, "both", "Off", _}} =
             Cure.Elab.Equation.resolve_member(env, "both", "Off")

    assert {:ok, %{pattern_key: "both/On/On"}} = Cure.Elab.Equation.resolve_member(env, "both", "On")

    assert {:ok, %{pattern_key: "both/On/Off"}} =
             Cure.Elab.Equation.resolve_path(env, "both", ["On", "Off"])

    assert Enum.all?(equations, &Env.certified?(env, &1.theorem))
  end

  test "impossible indexed paths are absent and guarded constructor collisions are not published" do
    impossible = """
    mod ImpossibleEquations
      type Nat = Z | S(Nat)
      type Vec(a) indices (n: Nat)
        vnil : Vec(a, Z)
        vcons : (k: Nat) -> a -> Vec(a, k) -> Vec(a, S(k))
      fn only_nil(v: Vec(Nat, Z)) -> Nat = match v
        vnil() -> Z()
    end
    """

    assert {:ok, impossible_env} = Program.elaborate(impossible)
    assert [%{pattern_key: "only_nil/vnil"}] = Env.equations(impossible_env, :only_nil)

    guarded = """
    mod GuardedEquations
      type Nat = Z | S(Nat)
      fn is_zero(n: Nat) -> Bool = match n
        Z() -> true
        S(k) -> false
      fn classify(n: Nat) -> Nat = match n
        S(k) when is_zero(k) -> Z()
        S(k) -> S(Z())
        Z() -> S(S(Z()))
    end
    """

    assert {:ok, guarded_env} = Program.elaborate(guarded)

    # The two authored S clauses share a constructor path. Until guards are
    # represented in structural equation keys, neither may masquerade as the
    # unique `classify.S`; the unguarded Z path remains safely discoverable.
    assert [%{pattern_key: "classify/Z"}] = Env.equations(guarded_env, :classify)

    assert {:ok, %{pattern_key: "classify/Z"}} =
             Cure.Elab.Equation.resolve_member(guarded_env, "classify", "Z")

    assert {:error, {:defining_equation_unavailable, :unknown_equation, "classify", "S", _}} =
             Cure.Elab.Equation.resolve_member(guarded_env, "classify", "S")
  end

  test "complete nested member paths elaborate to the selected equation" do
    source = """
    mod NestedEquationUse
      type Bit = Off | On

      fn both(left: Bit, right: Bit) -> Bit = match left
        Off -> Off
        On -> match right
          Off -> Off
          On -> On

      fn expose() = both.On.Off
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert %{body: {:global, :"NestedEquationUse#both$equation$On$Off"}} = Env.get_def(env, :expose)
  end

  test "private defining equations remain available only inside their owner module" do
    source = """
    mod PrivateEquations
      type Bit = Off | On
      local fn hidden(bit: Bit) -> Bit = match bit
        Off -> On
        On -> Off
    end
    """

    assert {:ok, owner_env} = Program.elaborate(source)
    assert {:ok, %{visibility: :private}} = Cure.Elab.Equation.resolve_member(owner_env, "hidden", "Off")

    consumer_env = Env.with_owner(owner_env, "Consumer")

    assert {:error, {:defining_equation_unavailable, :inaccessible_equation, "hidden", "Off", [_]}} =
             Cure.Elab.Equation.resolve_member(consumer_env, "hidden", "Off")
  end

  test "public equations survive module interfaces and imports", %{root: root} do
    module_path = Path.join(root, "provider.cure")

    File.write!(module_path, """
    mod EquationProvider
      type Bit = Off | On
      fn flip(bit: Bit) -> Bit = match bit
        Off -> On
        On -> Off
    end
    """)

    assert {:ok, interface} = Program.module_interface("EquationProvider", module_path)
    assert [%{pattern_key: "flip/Off"}, %{pattern_key: "flip/On"}] = Env.equations(interface.export_env, :flip)

    assert {:ok, consumer} =
             Program.elaborate("""
             mod EquationConsumer
               use EquationProvider
               fn expose() = flip.Off
             end
             """)

    assert %{body: {:global, :"EquationProvider#flip$equation$Off"}} = Env.get_def(consumer, :expose)
  end

  test "equation metadata contributes deterministically to interface hashes", %{root: root} do
    module_path = Path.join(root, "hash_provider.cure")

    File.write!(module_path, """
    mod EquationHashProvider
      type Bit = Off | On
      fn flip(bit: Bit) -> Bit = match bit
        Off -> On
        On -> Off
    end
    """)

    assert {:ok, first} = Program.module_interface("EquationHashProvider", module_path)
    Program.invalidate_module_interface(module_path)
    assert {:ok, second} = Program.module_interface("EquationHashProvider", module_path)

    assert Cure.Compiler.ModuleInterface.semantic_hash(first.export_env) ==
             Cure.Compiler.ModuleInterface.semantic_hash(second.export_env)
  end

  test "polymorphic constructor fields and dependent result carriers remain kernel checked" do
    assert {:ok, set} =
             Cure.Compiler.Artifacts.open_verified_set(
               kind: :stdlib,
               candidates: Cure.Stdlib.Paths.beam_dirs()
             )

    assert {:ok, interfaces} =
             Cure.Compiler.ModulePipeline.Interface.load_roots([set.artifact_root])

    assert {:ok, universe} = Cure.Compiler.ModulePipeline.Interface.environment(interfaces)

    assert append_equations = Env.equations(universe, :"Std.List#append")
    assert Enum.map(append_equations, & &1.pattern_key) |> Enum.sort() == ["append/Cons", "append/Nil"]
    cons_equation = Enum.find(append_equations, &(&1.pattern_key == "append/Cons"))
    assert :ok = Kernel.check_def(universe, cons_equation.theorem)

    assert [second_equation] = Env.equations(universe, :"Std.Sigma#sigma_second")
    assert second_equation.pattern_key == "sigma_second/mk_pair"
    assert :ok = Kernel.check_def(universe, second_equation.theorem)

    for owner <- [:"Std.Equivalent#sym", :"Std.Equivalent#trans", :"Std.Equivalent#cong"] do
      assert [equation] = Env.equations(universe, owner)
      assert :ok = Kernel.check_def(universe, equation.theorem)
    end

    assert Enum.map(Env.equations(universe, :"Std.Vector#lookup"), & &1.pattern_key)
           |> Enum.sort() ==
             ["lookup/First/prepend", "lookup/Next/prepend"]

    for equation <- Env.equations(universe, :"Std.Vector#lookup") do
      assert :ok = Kernel.check_def(universe, equation.theorem)
    end
  end

  test "generated proof definitions are compile-time-only unless an ordinary source definition reaches them" do
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(@source, emit_events: false)
    {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)
    assert {:ok, _env, locals} = Program.check_ast_with_locals(ast)
    assert :"EquationFixture#identity$equation$Z" in locals
    refute :"EquationFixture#identity$equation$S" in locals
  end

  test "the kernel rejects a forged defining equation body" do
    assert {:ok, env} = Program.elaborate(@source)
    [equation | _] = Env.equations(env, :identity)
    forged = put_in(env.defs[equation.theorem].body, Cure.Elab.Rewrite.mk_refl({:int_lit, 99}))
    assert {:error, _} = Kernel.check_def(forged, equation.theorem)
  end

  test "unknown members on functions with defining equations report E114 at elaboration" do
    source = """
    mod UnknownEquation
      type Bit = Off | On
      fn flip(bit: Bit) -> Bit = match bit
        Off -> On
        On -> Off
      fn bad() = flip.Missing
    end
    """

    assert {:error, {:defining_equation_unavailable, %Cure.Diagnostic.DefiningEquationProblem{} = problem}} =
             source |> Program.elaborate() |> Program.semantic_result()

    assert problem.kind == :unknown_equation
    assert problem.owner == "flip"
    assert problem.member == "Missing"
    assert problem.equation_use
  end
end
