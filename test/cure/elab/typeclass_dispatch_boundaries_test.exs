defmodule Cure.Elab.TypeclassDispatchBoundariesTest do
  @moduledoc """
  Three places where `interface`/`implementation` promised something it did not deliver. Two are
  fixed here; the third is a feature gap, and this file pins exactly where its edge is so it
  fails loudly instead of quietly.

  ## An unqualified method call picked an interface by map-iteration order

  `Interface.for_method/2` is the sole lookup `Resolve.method_call` uses to find the interface
  owning an unqualified `size(x)`, and it is `Enum.find_value/2` over the whole `env.interfaces`
  map — the FIRST interface, in unspecified order, whose method table holds the name. Nothing
  anywhere checked that a method name is unique across in-scope interfaces, so two interfaces
  both declaring `size` left every call bound to whichever descriptor the map yielded first, with
  no diagnostic at either the declaration or the call. Idris2 and Lean 4 both make an
  undisambiguatable unqualified reference a compile error rather than an arbitrary pick; Cure has
  no qualified method-call syntax, so the ambiguity is reported where it is created.

  ## The named-implementation escape hatch was inert

  Cure's coherence policy is global uniqueness plus named implementations as the escape hatch:
  `implementation Eqs for Int as strictInt` is meant to register under `:strictInt` "as an
  ordinary dictionary-valued binding … selected explicitly with plain record projection".
  `register_instance/5` only wrote the ref into `Coherence.named`, and `Coherence.lookup_named/2`
  had zero callers in `lib/` — nothing bound the atom `:strictInt` to anything, so no reference to
  it could ever resolve. The hatch the policy depends on to let an overlapping instance coexist
  was accepted at register time and permanently unreachable. It is now bound as an ordinary
  global of type `Iface(head)`, built from the instance's own ref (which `Resolve.dict_term/3`
  cannot see, since it consults only the anonymous registry).

  ## Higher-kinded abstract dispatch: a real gap, failing loudly

  `Interface.declare_dictionary_former/2` builds the Core dictionary record family only for a
  `:type` head kind; every other kind is a bare no-op whose comment claims the former "is built
  by the HKT resolution step". No such step exists. So `Functor` is never registered as a Core
  family, and a `where Functor(f)` constraint has nothing to build a dictionary value against.

  This is incompleteness, not unsoundness: abstract dispatch reports `{:no_instance, …}` rather
  than silently resolving to the wrong instance, and concrete dispatch never touches the path.
  It is also not really about HKT — the underlying gap is method-level generics, which
  `Interface`'s own moduledoc defers ("side-steps method-level generics until an instance
  actually forces the issue"). A kind-`Type` interface whose method introduces its own type
  variables fails the same way. Closing it means giving each dictionary field its own quantifiers
  rather than hoisting them to the family's parameters, which is a design change, not a fix.
  The tests below hold that boundary in place.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.{Coherence, Program}

  describe "a method name shared by two in-scope interfaces" do
    test "is rejected at the declaration that creates the ambiguity" do
      src = """
      mod M
        interface Eqs(a)
          fn size(x: a) -> Int
        interface Ord(a)
          fn size(x: a) -> Bool
      end
      """

      assert {:error, error} = Program.elaborate(src)
      assert {:ambiguous_method, :size, [:Eqs, :Ord]} = Program.semantic_error(error)
    end

    test "distinct method names across two interfaces are fine" do
      src = """
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
        interface Sized(a)
          fn size(x: a) -> Int
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end
  end

  describe "a named implementation is an ordinary dictionary-valued global" do
    @src """
    mod M
      interface Eqs(a)
        fn eqs(x: a, y: a) -> Bool
      implementation Eqs for Int as strictInt
        fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
    end
    """

    test "it is bound as a value of type Iface(head), not merely recorded in Coherence" do
      assert {:ok, env} = Program.elaborate(@src)

      assert {:ok, _ref} = Coherence.lookup_named(Env.coherence(env), :strictInt)

      def_ = Env.get_def(env, :strictInt)
      refute is_nil(def_), "a named implementation must be bound as an ordinary global value"
      assert def_.type == {:data, :"M#Eqs", [{:data, :"Std.Int#Int", [], []}], []}
      assert {:ctor, :"M#Eqs", [_eqs_method]} = def_.body
    end

    test "a caller can name it" do
      src = String.replace(@src, "end\n", "  fn pick() -> Int -> Int -> Bool = strictInt.eqs\nend\n")
      assert {:ok, _env} = Program.elaborate(src)
    end

    test "it coexists with an anonymous instance for the same interface and head" do
      # This is what the escape hatch is FOR: a second, overlapping instance.
      src = """
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
        implementation Eqs for Int
          fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
        implementation Eqs for Int as strictInt
          fn eqs(x: Int, y: Int) -> Bool = int_ne(x, y)
      end
      """

      assert {:ok, env} = Program.elaborate(src)
      assert Env.get_def(env, :strictInt)
    end
  end

  describe "higher-kinded interfaces: the boundary of what is implemented" do
    @functor """
    mod H
      fn lmap(xs: List(a), g: a -> b) -> List(b) =
        match xs
          [] -> []
          [h | t] -> [g(h) | lmap(t, g)]
      interface Functor(f)
        fn fmap(container: f(a), g: a -> b) -> f(b)
      implementation Functor for List
        fn fmap(container: List(a), g: a -> b) -> List(b) = lmap(container, g)
    """

    test "the head kind is inferred, but no Core dictionary family is declared" do
      assert {:ok, env} = Program.elaborate(@functor <> "end\n")

      assert Env.get_interface(env, :Functor).head_kind == {:arrow, :type, :type}

      refute Inductive.family?(env, :Functor),
             "if this now passes, the HKT dictionary former exists — delete this test and " <>
               "enable abstract dispatch below"
    end

    test "concrete dispatch works — it never needs the dictionary family" do
      src = @functor <> "  fn bump(xs: List(Int)) -> List(Int) = fmap(xs, fn(x) -> x + 1)\nend\n"
      assert {:ok, _env} = Program.elaborate(src)
    end

    test "abstract dispatch through a `where` constraint fails loudly, not silently" do
      src =
        @functor <>
          "  fn twice({f: Type -> Type}, {a: Type}, xs: f(a), g: a -> a) -> f(a) where Functor(f) =\n" <>
          "    fmap(fmap(xs, g), g)\nend\n"

      assert {:error, {:source_context, {:no_instance, :Functor, _}, _}} = Program.elaborate(src)
    end

    test "the underlying gap is method-level generics, not higher kinds" do
      # A kind-`Type` interface whose method introduces its own type variables fails too, so
      # declaring the HKT former alone would not be enough.
      src = """
      mod M
        interface Container(a)
          fn cmap(x: a, g: t -> u) -> a
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end
  end

  describe "an instance head is normalized through transparent typealiases before it is keyed" do
    # `Implementation.register/2` derived the coherence key's `head` straight from `meta[:for]`,
    # which the parser sets to the RAW SURFACE NAME of the `for` clause with zero unfolding. A
    # `typealias` is a transparent synonym at the type-checking level, but `for Int` and
    # `for MyInt` keyed two DIFFERENT atoms, so both anonymous instances registered — two live
    # dictionaries for what is definitionally one type, and `eqs` could compute two different
    # answers depending on which spelling the call site used. Idris/Agda/Lean/Rust all resolve an
    # instance head to its normal form before comparing.
    @iface "  interface Eqs(a)\n    fn eqs(x: a, y: a) -> Bool\n"
    defp for_int(body), do: "  implementation Eqs for Int\n    fn eqs(x: Int, y: Int) -> Bool = #{body}\n"

    test "an instance for Int and one for a transparent alias of Int overlap" do
      src =
        "mod M\n  typealias MyInt = Int\n" <>
          @iface <>
          for_int("int_eq(x, y)") <>
          "  implementation Eqs for MyInt\n    fn eqs(x: MyInt, y: MyInt) -> Bool = int_eq(x, y)\nend\n"

      assert {:error, {:overlapping_instance, %{interface: :Eqs, head: :"Std.Int#Int"}}} =
               Program.elaborate(src)
    end

    test "a lone alias instance registers under the unfolded head, so bare `Int` dispatch finds it" do
      # The guard against a normalizer that rejects overlap by collapsing every head to one atom.
      src =
        "mod M\n  typealias MyInt = Int\n" <>
          @iface <>
          "  implementation Eqs for MyInt\n    fn eqs(x: MyInt, y: MyInt) -> Bool = int_eq(x, y)\n" <>
          "  fn use_it(a: Int, b: Int) -> Bool = eqs(a, b)\nend\n"

      assert {:ok, env} = Program.elaborate(src)

      assert {:ok, %{head: :"Std.Int#Int"}} =
               Coherence.lookup_anon(Env.coherence(env), :Eqs, :"Std.Int#Int")
    end

    test "an alias chain unfolds all the way to the head" do
      src =
        "mod M\n  typealias MyInt = Int\n  typealias Yours = MyInt\n" <>
          @iface <>
          for_int("int_eq(x, y)") <>
          "  implementation Eqs for Yours\n    fn eqs(x: Yours, y: Yours) -> Bool = int_eq(x, y)\nend\n"

      assert {:error, {:overlapping_instance, %{interface: :Eqs, head: :"Std.Int#Int"}}} =
               Program.elaborate(src)
    end

    test "an alias of a data family resolves to the family, not the alias name" do
      src =
        "mod M\n  type Col = Red | Blue\n  typealias C = Col\n" <>
          @iface <>
          "  implementation Eqs for C\n    fn eqs(x: C, y: C) -> Bool = struct_eq(x, y)\n" <>
          "  fn use_it(a: Col, b: Col) -> Bool = eqs(a, b)\nend\n"

      assert {:ok, env} = Program.elaborate(src)
      assert {:ok, %{head: :"M#Col"}} = Coherence.lookup_anon(Env.coherence(env), :Eqs, :"M#Col")
    end
  end
end
