defmodule Cure.Elab.CanonicalDefinitionIdentityTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Emit, Name, Program}

  test "local helper identities and Core calls are canonical in either declaration order" do
    bodies = [
      "local fn same() -> Int = 1\n  local fn matches() -> Int = same()",
      "local fn matches() -> Int = same()\n  local fn same() -> Int = 1"
    ]

    for body <- bodies do
      source = "mod RegexFixture\n  #{body}\n  fn run() -> Int = matches()\nend\n"
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      {:ok, ast} = Parser.parse(tokens, emit_events: false)
      assert {:ok, env, locals} = Program.check_ast_with_locals(ast)

      assert MapSet.new(locals) ==
               MapSet.new([
                 :"RegexFixture#same",
                 :"RegexFixture#matches",
                 :"RegexFixture#run"
               ])

      assert %{body: matches_body} = Map.fetch!(env.defs, :"RegexFixture#matches")
      assert contains_term?(matches_body, {:global, :"RegexFixture#same"})
      refute contains_term?(matches_body, {:global, :same})

      reachable = Program.reachable_def_names(env, [:run])

      assert reachable == [
               :"RegexFixture#matches",
               :"RegexFixture#run",
               :"RegexFixture#same"
             ]

      assert Enum.all?(reachable, &Map.has_key?(env.defs, &1))
      assert Enum.all?(reachable, &Name.qualified?/1)

      module = :"Cure.Test.RegexFixture#{System.unique_integer([:positive])}"
      assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: reachable)
      assert apply(module, :run, []) == 1
    end
  end

  # `run` is also the bare spelling of a kernel builtin op (`:effect_run`, seeded
  # by `Cure.Core.Builtins.seed_run/1` alongside the 32 arithmetic ops). Builtin
  # ops are body-less and are never emitted as function forms, so if an authored
  # root spelling resolves to the ambient bare key instead of to this module's own
  # canonical one, the function silently drops out of the emission set — the
  # module compiles to a BEAM form that does not contain it.
  #
  # A local definition shadows an ambient one everywhere else in the language;
  # selecting an emission root by authored spelling has to obey the same rule.
  test "a local definition whose name matches a builtin op still emits" do
    source = """
    mod BuiltinNameShadow
      fn run() -> Int = 41
      fn start() -> Int = run() + 1
    end
    """

    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env, _locals} = Program.check_ast_with_locals(ast)

    # Selected by the colliding spelling itself, which is where the ambient key
    # wins: a builtin-op def is body-less, so `collect_reachable/4` returns
    # without recording anything and the root vanishes.
    assert Program.reachable_def_names(env, [:run]) == [:"BuiltinNameShadow#run"]

    reachable = Program.reachable_def_names(env, [:run, :start])

    assert reachable == [
             :"BuiltinNameShadow#run",
             :"BuiltinNameShadow#start"
           ]

    module = :"Cure.Test.BuiltinNameShadow#{System.unique_integer([:positive])}"

    assert {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: reachable)

    assert apply(module, :start, []) == 42
    assert apply(module, :run, []) == 41
  end

  test "reachability never guesses a bare Core edge from a matching suffix" do
    env =
      Cure.Core.Env.empty()
      |> Cure.Core.Env.with_owner("Fixture")
      |> Cure.Core.Env.add_def(:same, {:int_type}, {:int_lit, 1})
      |> Cure.Core.Env.add_def(:run, {:int_type}, {:global, :same})

    assert Program.reachable_def_names(env, [:run]) == [:"Fixture#run"]

    assert {:error, {:emission_closure_missing, %{definition: :same, referenced_by: :"Fixture#run", module: "Fixture"}}} =
             Emit.compile_forms(env, :Fixture, [:"Fixture#run"])
  end

  test "emission roots never recover a missing local through a unique foreign suffix" do
    env =
      Cure.Core.Env.empty()
      |> Cure.Core.Env.with_owner("Fixture")
      |> Cure.Core.Env.add_def(:"Other#same", {:int_type}, {:int_lit, 1})

    assert {:error, {:emission_closure_missing, %{definition: :"Fixture#same", referenced_by: nil, module: "Fixture"}}} =
             Emit.validate_emission_closure(env, [:same])
  end

  test "a legacy origins map cannot rekey a definition during emission" do
    env =
      Cure.Core.Env.empty()
      |> Cure.Core.Env.add_def(:helper, {:int_type}, {:int_lit, 1})
      |> Cure.Core.Env.add_def(:run, {:int_type}, {:global, :helper})

    forms = Emit.module_forms(env, :"Cure.IdentityOrigins", [:run], %{helper: :"Cure.WrongOwner"})
    encoded = :erlang.term_to_binary(forms)

    refute encoded =~ "Cure.WrongOwner"
  end

  test "overload members and their callers use discriminated canonical keys" do
    source = """
    mod IdentityOverload
      type Meters = MkM(Int)
      type Grams = MkG(Int)
      fn choose(a: Meters) -> Meters = a
      fn choose(a: Grams) -> Grams = a
      fn meters() -> Meters = choose(MkM(1))
      fn grams() -> Grams = choose(MkG(2))
    """

    assert {:ok, env} = Program.elaborate(source)
    assert globals(env.defs[:"IdentityOverload#meters"].body) == [:"IdentityOverload#choose~0"]
    assert globals(env.defs[:"IdentityOverload#grams"].body) == [:"IdentityOverload#choose~1"]

    assert Program.reachable_def_names(env, [:meters, :grams]) == [
             :"IdentityOverload#choose~0",
             :"IdentityOverload#choose~1",
             :"IdentityOverload#grams",
             :"IdentityOverload#meters"
           ]
  end

  test "a global reached only through a lambda remains canonical and emit-reachable" do
    source = """
    mod IdentityLambda
      fn apply(f: (Int) -> Int, value: Int) -> Int = f(value)
      fn helper(value: Int) -> Int = value + 1
      fn run(value: Int) -> Int = apply(fn(item) -> helper(item), value)
    """

    assert {:ok, env} = Program.elaborate(source)
    run_globals = globals(env.defs[:"IdentityLambda#run"].body)
    assert :"IdentityLambda#apply" in run_globals
    assert :"IdentityLambda#helper" in run_globals
    refute :helper in run_globals

    assert Program.reachable_def_names(env, [:run]) == [
             :"IdentityLambda#apply",
             :"IdentityLambda#helper",
             :"IdentityLambda#run"
           ]
  end

  test "dictionary selection and constrained calls close over canonical definitions" do
    source = """
    mod IdentityDictionary
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      fn same({a: Type}, x: a, y: a) -> Bool where Eqs(a) = eqs(x, y)
      fn run(x: Int, y: Int) -> Bool = same(x, y)
    """

    assert {:ok, env} = Program.elaborate(source)
    reachable = Program.reachable_def_names(env, [:run])

    assert :"IdentityDictionary#same" in reachable
    assert :"IdentityDictionary#__impl_Eqs_Std.Int#Int_eqs" in reachable
    assert Enum.all?(reachable, &Name.qualified?/1)
    assert Enum.all?(reachable, &Map.has_key?(env.defs, &1))
    assert :ok = Emit.validate_emission_closure(env, reachable)
  end

  property "generated local dependency chains retain one canonical identity and valid closure" do
    check all(chain_length <- integer(1..20), max_runs: 30) do
      owner = "GeneratedIdentity"

      env =
        Enum.reduce(0..chain_length, Cure.Core.Env.empty() |> Cure.Core.Env.with_owner(owner), fn index, env ->
          body =
            if index == 0,
              do: {:int_lit, 0},
              else: {:global, Name.qualify(owner, "step#{index - 1}")}

          Cure.Core.Env.add_def(env, String.to_atom("step#{index}"), {:int_type}, body)
        end)

      root = String.to_atom("step#{chain_length}")
      reachable = Program.reachable_def_names(env, [root])

      assert length(reachable) == chain_length + 1
      assert Enum.all?(reachable, &Name.qualified?/1)
      assert Enum.all?(reachable, &Map.has_key?(env.defs, &1))
      assert :ok = Emit.validate_emission_closure(env, reachable)
    end
  end

  defp contains_term?(term, wanted) when term == wanted, do: true

  defp contains_term?(term, wanted) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.any?(&contains_term?(&1, wanted))

  defp contains_term?(term, wanted) when is_list(term),
    do: Enum.any?(term, &contains_term?(&1, wanted))

  defp contains_term?(_term, _wanted), do: false

  defp globals({:global, name}), do: [name]

  defp globals(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.flat_map(&globals/1) |> Enum.uniq()

  defp globals(terms) when is_list(terms), do: terms |> Enum.flat_map(&globals/1) |> Enum.uniq()
  defp globals(_term), do: []
end
