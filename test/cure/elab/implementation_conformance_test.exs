defmodule Cure.Elab.ImplementationConformanceTest do
  @moduledoc """
  Regression: an implementation is checked against its interface at the DECLARATION.

  An implementation is a record literal, checked field-by-field against the record's
  declared field types (Idris 2, Lean 4). Cure took each instance clause verbatim, renamed
  it, and derived the mangled global's Pi type from the CLAUSE's own params/return_type —
  never from the interface's `type_ast`. Nothing reconciled the two.

  Two consequences, both fixed here:

    * a clause whose declared type diverged from the interface's registered without
      complaint. Every USE site then failed with a bare
      `{:conversion_failure, {:int_type}, {:data, :Bool, [], []}}` blaming the caller
      instead of the implementation that broke its contract. (Not a soundness hole — the
      mismatch is caught downstream at concrete and dictionary sites alike — but the
      diagnostic pointed at the wrong code.)

    * a clause naming no interface method was never looked at. `build_methods/5` iterates
      the INTERFACE's `method_order` and searches the body by exact name, so a typo
      (`eqz` for `eqs`) contributed nothing and produced no diagnostic. When the intended
      method had a default, the implementation registered anyway — silently using the
      default and discarding the author's clause.

  Conformance is checked up to renaming of the method's non-head type variables, so
  `fmap(g: (x) -> y, container: List(x)) -> List(y)` still implements
  `fmap(g: (a) -> b, container: f(a)) -> f(b)`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  describe "signature conformance" do
    test "a clause whose return type diverges from the interface is rejected at the declaration" do
      src = """
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
        implementation Eqs for Int
          fn eqs(x: Int, y: Int) -> Int = 42
      end
      """

      assert {:error, {:method_signature_mismatch, %{interface: :Eqs, method: :eqs}}} = Program.elaborate(src)
    end

    test "a clause whose parameter type diverges from the interface is rejected" do
      src = """
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
        implementation Eqs for Int
          fn eqs(x: Int, y: Bool) -> Bool = true
      end
      """

      assert {:error, {:method_signature_mismatch, %{interface: :Eqs, method: :eqs}}} = Program.elaborate(src)
    end

    test "a conforming first-order implementation is accepted" do
      src = """
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
        implementation Eqs for Int
          fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "a higher-kinded implementation may rename the method's own type variables" do
      src = """
      mod M
        fn lmap(xs: List(a), g: a -> b) -> List(b) =
          match xs
            [] -> []
            [h | t] -> [g(h) | lmap(t, g)]
        interface Functor(f)
          fn fmap(container: f(a), g: a -> b) -> f(b)
        implementation Functor for List
          fn fmap(container: List(x), g: x -> y) -> List(y) = lmap(container, g)
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "a higher-kinded implementation that does not instantiate the head is rejected" do
      # `container: List(a)` is required; `Vector(a)` implements a different functor.
      src = """
      mod M
        interface Functor(f)
          fn fmap(container: f(a), g: a -> b) -> f(b)
        implementation Functor for List
          fn fmap(container: List(a), g: a -> b) -> Bool = true
      end
      """

      assert {:error, {:method_signature_mismatch, %{interface: :Functor, method: :fmap}}} = Program.elaborate(src)
    end
  end

  describe "stray clauses" do
    test "a clause naming no interface method is rejected even when defaults could cover it" do
      src = """
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool = true
          fn nes(x: a, y: a) -> Bool = true
        implementation Eqs for Int
          fn eqz(x: Int, y: Int) -> Bool = int_eq(x, y)
      end
      """

      assert {:error, {:unknown_interface_method, %{interface: :Eqs, method: :eqz}}} = Program.elaborate(src)
    end

    test "an implementation relying entirely on interface defaults is still accepted" do
      src = """
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool = true
        implementation Eqs for Int
      end
      """

      assert {:ok, _env} = Program.elaborate(src)
    end
  end

  describe "required methods" do
    test "an omitted method without an interface default retains implementation context" do
      src = """
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool
          fn nes(x: a, y: a) -> Bool
        implementation Eqs for Int
          fn eqs(x: Int, y: Int) -> Bool = int_eq(x, y)
      end
      """

      assert {:error,
              {:missing_method, %{interface: :Eqs, method: :nes, head: head, for: "Int", span: %Cure.Diagnostic.Span{}}}} =
               Program.elaborate(src)

      assert Cure.Elab.Name.base(head) == "Int"
    end
  end

  describe "implementation heads" do
    test "a value cannot be used as an implementation head" do
      src = """
      mod M
        interface Eqs(a)
          fn eqs(x: a, y: a) -> Bool = true
        implementation Eqs for 1
      end
      """

      assert {:error,
              {:instance_head_ill_formed,
               %{reason: :not_type_head, interface: :Eqs, for: "1", span: %Cure.Diagnostic.Span{}}}} =
               Program.elaborate(src)
    end
  end
end
