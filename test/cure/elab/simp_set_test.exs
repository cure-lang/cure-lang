defmodule Cure.Elab.SimpSetTest do
  use ExUnit.Case, async: false

  alias Cure.Core.{Context, Env, Kernel, Validator}
  alias Cure.Elab.{Program, ProofGoal, Rewrite}

  @provider """
  mod SimpProvider
    use Std.Equivalent
    type Nat = Z | S(Nat)
    fn plus(left: Nat, right: Nat) -> Nat = match left
      Z() -> right
      S(previous) -> S(plus(previous, right))

    @simp
    fn plus_zero_right(value: Nat) -> Equivalent(Nat, plus(value, Z()), value) = induction value
      case Z => reflexive(Z())
      case S(previous, induction_hypothesis) =>
        rewrite induction_hypothesis in reflexive(S(previous))
  end
  """

  defp with_consumer(source, body) do
    String.replace(source, ~r/end\s*$/, """
      fn reduced(value: Nat) -> Equivalent(Nat, plus(plus(value, Z()), Z()), value) = proof chain
        plus(plus(value, Z()), Z())
          == value
          because
            #{body}
    end
    """)
  end

  test "an explicitly tagged quantified induction theorem simplifies to a kernel checked proof" do
    assert {:ok, env} = Program.elaborate(with_consumer(@provider, "simplify"))
    assert :ok = Kernel.check_def(env, :"SimpProvider#plus_zero_right")
    assert :ok = Kernel.check_def(env, :"SimpProvider#reduced")
    assert Env.certified?(env, :"SimpProvider#plus_zero_right")

    assert [%{simp: true, arity: 1}] =
             env.lemmas
             |> Map.values()
             |> List.flatten()
             |> Enum.filter(&(&1.name == :"SimpProvider#plus_zero_right"))
             |> Enum.uniq()

    nodes = env |> Env.get_def(:reduced) |> Map.fetch!(:body) |> Validator.nodes()
    assert Enum.any?(nodes, &match?({:global, :"SimpProvider#plus_zero_right"}, &1))
  end

  test "@lemma(:simp) uses the supported decorator argument syntax" do
    source = String.replace(@provider, "@simp", "@lemma(:simp)")
    assert {:ok, env} = Program.elaborate(with_consumer(source, "simplify"))
    assert :ok = Kernel.check_def(env, :"SimpProvider#reduced")
  end

  test "legacy safe @lemma remains ambient and supports quantified specialization" do
    source = String.replace(@provider, "@simp", "@lemma")
    assert {:ok, env} = Program.elaborate(with_consumer(source, "simplify"))
    assert :ok = Kernel.check_def(env, :"SimpProvider#reduced")
  end

  test "explicit instantiated lemma rules accept Core proof types from elaboration" do
    assert {:ok, env} = Program.elaborate(with_consumer(@provider, "simplify using [plus_zero_right(value)]"))
    assert :ok = Kernel.check_def(env, :"SimpProvider#reduced")
  end

  test "non-decreasing explicit simp declarations are rejected before elaborating the body" do
    for {left, right} <- [{"x", "x"}, {"x", "S(x)"}, {"S(x)", "S(x)"}] do
      source = """
      mod BadSimp
        type Nat = Z | S(Nat)
        @simp
        fn looping(x: Nat) -> Equivalent(Nat, #{left}, #{right}) = missing_proof
      end
      """

      assert {:error, {:invalid_simp_lemma, "looping", :non_decreasing_orientation}} =
               source |> Program.elaborate() |> Program.semantic_result()
    end
  end

  test "a reverse rule completing a loop is rejected at declaration time" do
    source =
      String.replace(@provider, ~r/end\s*$/, """
        @simp
        fn reverse(value: Nat) -> Equivalent(Nat, value, plus(value, Z())) = missing_proof
      end
      """)

    assert {:error, {:invalid_simp_lemma, "reverse", :non_decreasing_orientation}} =
             source |> Program.elaborate() |> Program.semantic_result()
  end

  test "syntactically smaller rules cannot duplicate a quantified argument" do
    source = """
    mod DuplicatingSimp
      type Nat = Z | S(Nat)
      fn f(x: Nat, y: Nat) -> Nat = x
      @simp
      fn duplicate(x: Nat) -> Equivalent(Nat, f(S(S(S(x))), Z), f(x, x)) = missing_proof
    end
    """

    assert {:error, {:invalid_simp_lemma, "duplicate", :variable_duplication}} =
             source |> Program.elaborate() |> Program.semantic_result()
  end

  test "ordinary non-decreasing @lemma declarations remain valid proof-search facts" do
    source = """
    mod LegacyLemma
      @lemma
      fn same(x: Int) -> Equivalent(Int, x, x) = reflexive(x)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "simp declarations must conclude equality and accept no extra arguments" do
    assert {:error, {:invalid_simp_lemma, "bad", :not_equality}} =
             Program.semantic_result(Program.elaborate("mod NotEquality\n  @simp\n  fn bad(x: Int) -> Int = x\nend"))

    source = String.replace(@provider, "@simp", "@simp(:unexpected)")

    assert {:error, {:invalid_simp_lemma, "plus_zero_right", :unexpected_arguments}} =
             source |> Program.elaborate() |> Program.semantic_result()
  end

  test "simp metadata survives a module interface and imported rules actually simplify" do
    root = Path.join(System.tmp_dir!(), "cure_simp_#{System.unique_integer([:positive])}")
    File.mkdir_p!(root)
    path = Path.join(root, "provider.cure")
    File.write!(path, String.replace(@provider, "type Nat = Z | S(Nat)", "use Std.Nat"))
    previous = Process.put(:cure_source_roots, [root])

    on_exit(fn -> File.rm_rf!(root) end)

    try do
      assert {:ok, interface} = Program.module_interface("SimpProvider", path)
      assert Enum.any?(interface.export_env.lemmas |> Map.values() |> List.flatten(), &Map.get(&1, :simp, false))

      assert {:ok, env} =
               Program.elaborate("""
               mod SimpConsumer
                 use SimpProvider
                 fn reduced(value: Nat) -> Equivalent(Nat, plus(value, Z()), value) = proof chain
                   plus(value, Z())
                     == value
                     because
                       simplify
               end
               """)

      assert :ok = Kernel.check_def(env, :"SimpConsumer#reduced")
    after
      if previous, do: Process.put(:cure_source_roots, previous), else: Process.delete(:cure_source_roots)
    end
  end

  test "noncertified and forged lemma bodies cannot produce ambient evidence" do
    assert {:ok, env} = Program.elaborate(@provider)
    name = :"SimpProvider#plus_zero_right"
    uncertified = %{env | certified: MapSet.delete(env.certified, name)}
    forged = put_in(env.defs[name].body, Rewrite.mk_refl({:ctor, :"SimpProvider#Z", []}))

    nat = {:data, :"SimpProvider#Nat", [], []}
    left = {:app, {:app, {:global, :"SimpProvider#plus"}, {:var, 0}}, {:ctor, :"SimpProvider#Z", []}}
    expected = Rewrite.mk_eq(nat, left, {:var, 0})
    statement = {:proof_justification, [], [{:simplify_command, [], []}]}

    for rejected <- [uncertified, forged] do
      context = rejected |> Context.empty() |> Context.extend({:vdata, :"SimpProvider#Nat", []})

      assert {:error, {:simplification_failed, _problem}} =
               ProofGoal.run(statement, expected, ["value"], context, rejected, 0)
    end
  end

  test "a valid theorem cannot specialize to a forged lemma registry proposition" do
    assert {:ok, env} = Program.elaborate(@provider)
    name = :"SimpProvider#plus_zero_right"
    equality = :"Std.Equivalent#Equivalent"
    nat = {:data, :"SimpProvider#Nat", [], []}
    left = {:app, {:app, {:global, :"SimpProvider#plus"}, {:var, 0}}, {:ctor, :"SimpProvider#Z", []}}
    wrong_right = {:ctor, :"SimpProvider#S", [{:var, 0}]}
    expected = Rewrite.mk_eq(nat, left, wrong_right)
    {:pi, grade, domain, _body} = Env.get_def(env, name).type

    forged =
      put_in(env.lemmas[equality], [
        %{name: name, type: {:pi, grade, domain, expected}, arity: 1, simp: true}
      ])

    context = forged |> Context.empty() |> Context.extend({:vdata, :"SimpProvider#Nat", []})
    statement = {:proof_justification, [], [{:simplify_command, [], []}]}

    assert {:error, {:simplification_failed, _problem}} =
             ProofGoal.run(statement, expected, ["value"], context, forged, 0)
  end
end
