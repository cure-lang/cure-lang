defmodule Cure.Elab.ResolutionTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Grade, Inductive}
  alias Cure.Elab.Resolution

  test "declaration registration establishes canonical family, ctor, and def identities" do
    env = Env.with_owner(Env.empty(), "Std.Nat")

    env =
      env
      |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
        Inductive.ctor(:Z, [], []),
        Inductive.ctor(:S, [{:n, {:data, :Nat, [], []}}], [])
      ])
      |> Env.add_def(
        :plus,
        {:pi, Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}},
        {:global, :plus}
      )

    assert Map.has_key?(env.families, :"Std.Nat#Nat")
    assert Map.has_key?(env.ctors, :"Std.Nat#Z")
    assert Map.has_key?(env.ctors, :"Std.Nat#S")
    assert Map.has_key?(env.defs, :"Std.Nat#plus")
    assert env.ctors[:"Std.Nat#S"].args == [{:n, {:data, :Nat, [], []}}]
  end

  test "qualified type and value paths resolve exact canonical keys" do
    env =
      Env.with_owner(Env.empty(), "Std.Nat")
      |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [Inductive.ctor(:Z, [], [])])

    assert Resolution.resolve_qualified(env, "Std.Nat.Z", :value) == {:ok, :"Std.Nat#Z"}
    assert Resolution.resolve_qualified(env, "Std.Nat", :type) == {:ok, :"Std.Nat#Nat"}
    assert Resolution.resolve_qualified(env, "Std.Nat.Nat", :type) == {:ok, :"Std.Nat#Nat"}
    assert Resolution.resolve_qualified(env, "Std.Bool.True", :value) == :error
  end

  test "qualified lookup never falls back to an unrelated bare key" do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Bool, [], [], 0), [Inductive.ctor(:True, [], [])])

    assert Resolution.resolve_qualified(env, "Std.Bool.True", :value) == :error
  end

  test "qualified availability does not open a module's names lexically" do
    env =
      %{
        Env.empty()
        | bare_modules: MapSet.new(),
          qualified_modules: MapSet.new(["Std.Regex"])
      }
      |> Env.add_def(:"Std.Regex#same", {:type, 0}, {:type, 0})

    assert Resolution.resolve_qualified(env, "Std.Regex.same", :value) ==
             {:ok, :"Std.Regex#same"}

    assert Resolution.resolve_bare(env, :same) == :none
  end

  test "transitive providers do not leak bare names" do
    env =
      %{
        Env.empty()
        | import_modules: MapSet.new(["Direct"]),
          bare_modules: MapSet.new(["Direct"]),
          qualified_modules: MapSet.new(["Direct", "Transitive"])
      }
      |> Env.add_def(:"Direct#open_name", {:type, 0}, {:type, 0})
      |> Env.add_def(:"Transitive#hidden_name", {:type, 0}, {:type, 0})

    assert Resolution.resolve_bare(env, :open_name) == {:ok, :"Direct#open_name"}
    assert Resolution.resolve_bare(env, :hidden_name) == :none

    assert Resolution.resolve_qualified(env, "Transitive.hidden_name", :value) ==
             {:ok, :"Transitive#hidden_name"}
  end

  test "bare lookup resolves one canonical provider and reports direct ambiguity" do
    env =
      %Env{import_modules: MapSet.new(["Std.Foo", "Std.Bar"])}
      |> Inductive.declare(Inductive.family(:"Std.Foo#Nat", [], [], 0), [
        Inductive.ctor(:"Std.Foo#Z", [], [])
      ])
      |> Inductive.declare(Inductive.family(:"Std.Bar#Nat", [], [], 0), [
        Inductive.ctor(:"Std.Bar#Z", [], [])
      ])

    assert {:ambiguous, owners} = Resolution.resolve_bare(env, :Nat)
    assert Enum.sort(owners) == ["Std.Bar", "Std.Foo"]
    assert Enum.sort(Resolution.ambiguous_modules(env, :Nat)) == ["Std.Bar", "Std.Foo"]
  end

  test "a direct import wins over an ambient prelude provider without changing either identity" do
    env =
      %{
        Env.empty()
        | import_modules: MapSet.new(["Direct"]),
          bare_modules: MapSet.new(["Direct", "Prelude"]),
          qualified_modules: MapSet.new(["Direct", "Prelude"])
      }
      |> Env.add_def(:"Direct#same", {:type, 0}, {:type, 0})
      |> Env.add_def(:"Prelude#same", {:type, 0}, {:type, 0})

    assert Resolution.resolve_bare(env, :same) == {:ok, :"Direct#same"}
    assert Resolution.resolve_qualified(env, "Prelude.same", :value) == {:ok, :"Prelude#same"}
  end

  test "the current module's canonical declaration wins a bare lookup" do
    env =
      Env.with_owner(Env.empty(), "Main")
      |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [])
      |> Inductive.declare(Inductive.family(:"Std.Nat#Nat", [], [], 0), [])

    assert Resolution.resolve_bare(env, :Nat) == {:ok, :"Main#Nat"}
    assert Resolution.ambiguous_modules(env, :Nat) == []
  end

  test "shadowed_origin reports canonical owner metadata" do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:"Std.Nat#Nat", [], [], 0), [
        Inductive.ctor(:"Std.Nat#Z", [], [])
      ])

    assert Resolution.shadowed_origin(env, :Nat) == {:ok, "Std.Nat", :"Std.Nat#Nat"}
  end
end
