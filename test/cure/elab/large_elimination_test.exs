defmodule Cure.Elab.LargeEliminationTest do
  @moduledoc """
  Large elimination: a value-scrutinee `match` whose branches return DIFFERENT
  types, i.e. a type-level selector `FocusShape : OpticKind -> Type`. This is the
  kernel capability that Std.Optic's kind-indexed representation rests on (spec
  2026-07-11-std-optic-design §4: `FocusShape(k)` selects the per-kind optic rep).

  The oracle twin is
  `test/oracle/largeelim/le01_focus_shape_selector.{cure,idr}`
  (cure=accept, idris=accept, relation=same). These tests lock in that the
  elaborator not only ACCEPTS the selector but genuinely REDUCES it: the negative
  control fails precisely because `FocusShape(AffineKind)` computes to `Two` and
  `MkUnit` is foreign to `Two`.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @selector """
    type OpticKind = LensKind | AffineKind | TraversalKind
    type Unit = MkUnit
    type Two = T | F
    fn FocusShape(k: OpticKind) -> Type = match k
      LensKind -> Unit
      AffineKind -> Two
      TraversalKind -> Unit
  """

  test "selector matching to different types elaborates, and reduces at each kind" do
    src = """
    mod LE
    #{@selector}
      fn mk_lens() -> FocusShape(LensKind) = MkUnit
      fn ok_affine() -> FocusShape(AffineKind) = T
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "negative control: a ctor foreign to the reduced type is rejected" do
    # `FocusShape(AffineKind)` reduces to `Two`; `MkUnit` is a ctor of `Unit`, not
    # `Two`, so this must be rejected. A pass here proves the selector genuinely
    # computes rather than accepting any body at a computed type.
    src = """
    mod LENeg
    #{@selector}
      fn bad() -> FocusShape(AffineKind) = MkUnit
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end

  # A type FAMILY applied to an argument in a Type-returning function BODY (a
  # type-level function). The signature path already splits a family application
  # into its param/index slots (`declarations.ex` `idx_to_core`), but the
  # EXPRESSION path (`elaborate_named_call_scoped`) did not — it resolved the head
  # to `{:data, Option, [], []}` and `{:app}`-chained the argument OUTSIDE the data
  # node, so the kernel saw a 0-param `Option` where the family needs one param and
  # rejected it with a false `:arg_arity`. This is the keystone that Std.Optic's
  # `FocusShape(k, a, s)` selector rests on: every branch returns a per-kind
  # representation type built by applying a family to the ambient type parameters.
  test "a parameterised family applied in a Type-returning body elaborates" do
    src = """
    mod TyFnBody
      use Std.Option
      fn F(a: Type) -> Type = Option(a)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "large-elim selector whose branches apply a family to an ambient parameter" do
    # The le02 oracle twin (test/oracle/largeelim/le02_selector_ambient_param):
    # `FocusShape(k, a)` matches on `k` but each branch returns a type built from
    # the other parameter `a`. Idris accepts the analogue routinely; Cure rejected
    # with `:arg_arity` until the expression-path family split landed.
    src = """
    mod LEAmbient
      use Std.Option
      type OpticKind = LensKind | AffineKind | TraversalKind
      type Pair(a: Type) = MkPair(a, a)
      fn FocusShape(k: OpticKind, a: Type) -> Type = match k
        LensKind -> Option(a)
        AffineKind -> Pair(a)
        TraversalKind -> Option(a)
      fn mk_lens(x: a) -> FocusShape(LensKind, a) = Some(x)
      fn mk_affine(x: a) -> FocusShape(AffineKind, a) = MkPair(x, x)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a tuple type is first-class in a Type-returning function body" do
    src = """
    mod LETupleBody
      type Choice = PairChoice

      fn Selected(choice: Choice) -> Type = match choice
        PairChoice -> Tuple(Int, Bool)

      fn witness() -> Selected(PairChoice) = %[1, true]
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a tuple type lowers when nested as a dependent family index" do
    src = """
    mod LETupleIndex
      type Box indices (content: Type)
        boxed : Box(content)

      fn witness() -> Box(Tuple(Int, Bool)) = boxed()
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a dependent match accepts explicit branches for every constructor" do
    src = """
    mod LEDependentDefault
      type Kind = Number | Truth

      fn Selected(kind: Kind) -> Type = match kind
        Number -> Int
        Truth -> Bool

      fn keep(kind: Kind, value: Selected(kind)) -> Selected(kind) = match kind
        Number -> value
        Truth -> value
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
