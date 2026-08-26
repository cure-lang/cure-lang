defmodule Cure.Elab.LambdaArgumentOrderTest do
  @moduledoc """
  Argument ORDER must not decide typability.

  An unannotated lambda argument declared BEFORE the argument that fixes its domain used to be
  rejected: the lambda's domain metavariable is only solved by the later argument, and arguments
  elaborate left to right.

      fn app2(g: a -> b, xs: List(a)) -> List(b) = lmap(xs, g)
      fn bump(xs: List(Int)) -> List(Int) = app2(fn(x) -> x + 10, xs)   # used to fail

  Swapping the two parameters made it elaborate. Nothing about interfaces was ever involved — it
  first surfaced through a higher-kinded `fmap(g, container)` declared in that order, which is why
  it was mistaken for a dispatch-head bug.

  Closed by completing the POSTPONEMENT that `bidir_app_slot` already started. It defers an
  argument it cannot infer (a placeholder metavariable holds the slot) precisely so a later
  sibling can solve what that argument needs. But the retry half, `resolve_deferred_slots`, only
  recovered a deferred argument's own family INDICES (`solve_deferred_domain`, constructor
  applications only). A lambda needs its DOMAIN, and once a sibling supplies it the codomain can
  be solved under the binder by inferring the body — the Miller solve `try_lambda_meta_pi`
  already implemented, which had been attempted only EAGERLY, when the domain was still open, and
  was never re-offered. Retrying it on the deferred queue is Idris 2's retry queue
  (`Core/Unify.idr`) / Agda's postponed constraints, in the small.

  The contract these tests hold now: order-independence for what IS determined, and a loud
  rejection for what genuinely is not. The last test is the guard — a lambda whose domain no
  sibling and no goal determines must still fail, or the postponement has become a licence to
  guess.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @lmap """
    fn lmap(xs: List(a), g: a -> b) -> List(b) =
      match xs
        [] -> []
        [h | t] -> [g(h) | lmap(t, g)]
  """

  defp elaborate(decls), do: Program.elaborate("mod M\n" <> @lmap <> decls <> "end\n")

  test "a lambda argument AFTER the argument that fixes its domain elaborates" do
    decls = """
      fn app2(xs: List(a), g: a -> b) -> List(b) = lmap(xs, g)
      fn bump(xs: List(Int)) -> List(Int) = app2(xs, fn(x) -> x + 10)
    """

    assert {:ok, _env} = elaborate(decls)
  end

  test "a lambda argument BEFORE the argument that fixes its domain elaborates" do
    decls = """
      fn app2(g: a -> b, xs: List(a)) -> List(b) = lmap(xs, g)
      fn bump(xs: List(Int)) -> List(Int) = app2(fn(x) -> x + 10, xs)
    """

    assert {:ok, _env} = elaborate(decls)
  end

  test "the same shape through a higher-kinded interface method" do
    src = """
    mod M
    #{@lmap}  interface Functor(f)
        fn fmap(g: a -> b, container: f(a)) -> f(b)
      implementation Functor for List
        fn fmap(g: a -> b, container: List(a)) -> List(b) = lmap(container, g)
      fn bump(xs: List(Int)) -> List(Int) = fmap(fn(x) -> x + 10, xs)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  # The postponement must not become a licence to accept a genuinely ambiguous
  # call. Nothing — no sibling argument, no return type — determines the lambda's
  # domain here, so it must still reject.
  test "a lambda argument no sibling and no goal determines still fails, loudly" do
    decls = """
      fn ap0(g: a -> b) -> Int = 0
      fn bump() -> Int = ap0(fn(x) -> x + 10)
    """

    assert {:error, _reason} = elaborate(decls)
  end

  # DISTINCT from the pinned gap above. Here the lambda's domain type has a SINGLE
  # type parameter that a LATER argument fully determines (`g: (a) -> a`, with `x: a`
  # fixing `a`) — so once the metavariable is solved the domain is fully concrete
  # `(a) -> a`, with NOTHING left to infer from the lambda body. This is exactly the
  # `set = over(o, fn(_) -> new, x)` shape in `Std.Optic`, which had to fall back to a
  # curried `const` helper. Unlike the `a -> b` cases, this is not the ordering
  # limitation — the deferred re-check simply mis-shifted the solved domain's de Bruijn
  # levels under the arrow binder (a `conversion_failure {:var,3} {:var,2}`), which is a
  # bug, not an inherent gap. With that fixed, the inline lambda elaborates.
  test "a lambda whose monomorphic domain a later argument fully fixes elaborates" do
    src = """
    mod M
    fn over2({a: Type}, g: (a) -> a, x: a) -> a = g(x)
    fn set3({a: Type}, new: a, x: a) -> a = over2(fn(ignored) -> new, x)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  # The same monomorphic `(a) -> a` lambda, but with its domain fixed by an EARLIER
  # argument (`x: a` before `g`), so the metavariable is already solved when the lambda
  # slot is reached — the "domain fully known" branch, a DIFFERENT code path than the
  # deferred one above. Both had the same de Bruijn mis-shift when the solved domain
  # carried free variables. This is the exact shape of `Std.Optic`'s
  # `set = over(o, fn(_) -> new, x)`, whose `over(o, g, x)` fixes the lambda's `a` from
  # the earlier `o : Optic(s, a, k)`.
  test "a lambda whose monomorphic domain an earlier argument fixes elaborates" do
    src = """
    mod M
    fn over3({a: Type}, x: a, g: (a) -> a) -> a = g(x)
    fn set4({a: Type}, new: a, x: a) -> a = over3(x, fn(ignored) -> new)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
