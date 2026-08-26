defmodule Cure.Elab.UnionCanonicalTest do
  @moduledoc """
  Canonicalisation is the keystone of anonymous unions: a union's IDENTITY is its
  canonical member list (flattened, nf-normalised, type-distinguishingly keyed,
  deduped, lexically sorted). That sorted key list names the generated family, so
  `Int | Bool` and `Bool | Int` are literally the same `{:data, name}`.

  These are unit tests over the raw canonicaliser, so they run against the BUILTIN
  seeded env (families `Bool`/`Equivalent`/`Int`/`List`/`Nat`/`Sigma`, primitives
  `Atom`/`Binary`/`Float`). `String` is `List(Char)` from the stdlib, not a
  builtin, so union members involving it are exercised in `union_test.exs`, which
  goes through `Program.elaborate/1` and gets the prelude.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Core.{Builtins, Env}
  alias Cure.Elab.{Declarations, Union}

  # Elaborate a prelude of declarations on top of the builtin-seeded env.
  defp env_for(src) do
    {:ok, toks} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(toks, emit_events: false)

    items =
      case ast do
        {:block, _, xs} -> xs
        x -> [x]
      end

    {:ok, env} =
      Enum.reduce_while(items, {:ok, Builtins.seed(Env.empty())}, fn decl, {:ok, env} ->
        case Declarations.elaborate(decl, env) do
          {:ok, env2} -> {:cont, {:ok, env2}}
          err -> {:halt, err}
        end
      end)

    env
  end

  defp base_env, do: env_for("")

  # Parse a bare type expression by wrapping it in a typealias and digging the RHS out.
  defp members(src, env) do
    {:ok, toks} = Lexer.tokenize("typealias T = " <> src <> "\n", emit_events: false)
    {:ok, {:type_annotation, _, [rhs]}} = Parser.parse(toks, emit_events: false)
    {:union_type, [], asts} = rhs
    Union.canonicalise(asts, [], env)
  end

  defp key(src, env) do
    {:ok, ms} = members(src, env)
    Union.family_key(ms, env)
  end

  describe "set semantics" do
    test "Int | Bool and Bool | Int produce the identical family key" do
      env = base_env()
      assert key("Int | Bool", env) == key("Bool | Int", env)
    end

    test "the key is sorted lexically" do
      env = base_env()
      assert key("Int | Bool", env) == :"Union<Std.Bool#Bool|Std.Int#Int>"
    end

    test "Int | Int dedupes to a single member (caller collapses to Int)" do
      env = base_env()
      assert {:ok, [%{key: "Std.Int#Int"}]} = members("Int | Int", env)
    end

    test "an applied type keys with its arguments" do
      env = base_env()
      assert key("List(Int) | Int", env) == :"Union<Std.Int#Int|Std.List#List(Std.Int#Int)>"
    end
  end

  describe "keys are type-distinguishing" do
    test "the string \"north\" and the atom :north do not collide" do
      # Keyed on VALUE alone, both would be `north`. The <TypeKey># prefix is what
      # keeps them apart — and what keeps their generated ctor names injective.
      env = base_env()
      {:ok, ms} = members("\"north\" | :north", env)
      keys = Enum.map(ms, & &1.key)

      assert length(Enum.uniq(keys)) == 2
      assert "String#\"north\"" in keys
      assert "Atom#:north" in keys
    end

    test "a bare numeral member defaults to Int" do
      env = base_env()
      {:ok, ms} = members("3 | Bool", env)

      assert Enum.any?(ms, &(&1.key == "Int#3"))
      # Nat-keyed literal members are unreachable in v1.
      refute Enum.any?(ms, &String.starts_with?(&1.key, "Nat#"))
    end
  end

  describe "alias unfolding" do
    test "typealias members unfold before keying" do
      env = env_for("typealias MyInt = Int\n")
      assert key("MyInt | Bool", env) == key("Int | Bool", env)
    end

    # NOTE: `(A | B) | C` flattening is tested in union_test.exs, not here — it needs
    # `typealias P = Int | String` to ELABORATE, which requires the idx_to_core
    # lowering clause, so it cannot run until that lands.
  end

  describe "full-nf soundness" do
    test "a certified global applied inside an index is folded, so it keys identically" do
      # `B2(idn(Z()))` and `B2(Z())` are the same type. Plain eval leaves the global
      # application `idn(Z())` stuck as a neutral inside the index; only full nf with
      # delta: :certified folds it. Without that, these two would produce two
      # DISTINCT generated families for one type — the whnf bug this pins.
      env =
        env_for("""
        type B2 indices (n: Nat)
          mk : B2(Z())
        fn idn(n: Nat) -> Nat = n
        """)

      assert key("B2(idn(Z())) | Bool", env) == key("B2(Z()) | Bool", env)
      assert key("B2(Z()) | Bool", env) == :"Union<B2(Std.Nat#Z)|Std.Bool#Bool>"
    end
  end

  describe "admission rules, checked on the CANONICAL member list" do
    test "rejects a non-ground member (a bare type variable)" do
      env = base_env()
      assert {:error, {:union_member_not_ground, _}} = members("a | Int", env)
    end

    # A literal unioned with its OWN type is ADMITTED — most-specific-wins, not
    # prohibition. A literal EXPRESSION injects into the literal member; anything else
    # injects via its inferred type. They never compete, so there is nothing to reject.
    test "a literal may be unioned with its own type — both members survive" do
      env = base_env()
      {:ok, ms} = members("Int | 3", env)

      assert Enum.map(ms, & &1.key) == ["Int#3", "Std.Int#Int"]
    end

    # The reason this case used to be interesting: it proves admission runs AFTER
    # normalisation. The alias must unfold to `Int` BEFORE keying, or the union would key
    # as `T2` and be a different family from `Int | 3`.
    test "a typealias member unfolds before keying, so T2 | 3 IS Int | 3" do
      env = env_for("typealias T2 = Int\n")

      assert key("T2 | 3", env) == key("Int | 3", env)
      assert key("T2 | 3", env) == :"Disjoint<Int#3|Std.Int#Int>"
    end
  end

  # The generated family's PREFIX is not cosmetic: it records whether the constructor tag
  # is load-bearing.
  #
  #   Union<…>    — members' erased value sets are pairwise DISJOINT, so the tagged sum
  #                 and a set union coincide and the tag is unobservable.
  #   Disjoint<…> — two members OVERLAP ({3} ⊆ Int; true/false ⊆ atoms), so this is ONLY
  #                 a disjoint sum: the tag is what keeps Int(3) and Lit3 apart.
  describe "Union<…> vs Disjoint<…>" do
    test "disjoint value sets keep the Union prefix" do
      env = base_env()

      # Int / Bool  — integers vs the atoms true/false. Nothing is both.
      assert key("Int | Bool", env) == :"Union<Std.Bool#Bool|Std.Int#Int>"
      # Int / List(Int) — integers vs lists.
      assert key("Int | List(Int)", env) == :"Union<Std.Int#Int|Std.List#List(Std.Int#Int)>"
      # a literal whose class no type member occupies
      assert key(":north | Int", env) == :"Union<Atom#:north|Std.Int#Int>"
    end

    test "a literal inside a type member's class is Disjoint" do
      env = base_env()

      # {3} subset-of Int: a value can be BOTH, so the tag is what separates them.
      assert key("Int | 3", env) == :"Disjoint<Int#3|Std.Int#Int>"
      assert key("3 | Nat", env) == :"Disjoint<Int#3|Std.Nat#Nat>"
      assert key(":north | Atom", env) == :"Disjoint<Atom|Atom#:north>"
    end

    test "a refining type member is Disjoint: Bool inside Atom" do
      env = base_env()

      # true/false are atoms, so Bool and Atom overlap.
      assert key("Bool | Atom", env) == :"Disjoint<Atom|Std.Bool#Bool>"
      # ...and it propagates through a wider union.
      assert key("Int | Bool | Atom", env) == :"Disjoint<Atom|Std.Bool#Bool|Std.Int#Int>"
    end

    test "two type members sharing a class are Disjoint" do
      env = base_env()

      # Both erase to Erlang integers.
      assert key("Int | Nat", env) == :"Disjoint<Std.Int#Int|Std.Nat#Nat>"
    end

    test "union_family?/1 recognises BOTH prefixes" do
      assert Union.union_family?(:"Union<Bool|Int>")
      assert Union.union_family?(:"Disjoint<Int|Int#3>")
      refute Union.union_family?(:Option)
    end
  end

  describe "ctor naming" do
    test "ctor names are qualified by the family key" do
      env = base_env()
      {:ok, ms} = members("Int | Bool", env)
      fk = Union.family_key(ms, env)
      int_m = Enum.find(ms, &(&1.key == "Std.Int#Int"))

      assert Union.ctor_key(fk, int_m) == :"Union<Std.Bool#Bool|Std.Int#Int>$Std.Int#Int"
    end

    test "union_family?/1 recognises a generated key and rejects a user type name" do
      assert Union.union_family?(:"Union<Bool|Int>")
      refute Union.union_family?(:Option)
    end
  end
end
