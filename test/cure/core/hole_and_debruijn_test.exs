defmodule Cure.Core.HoleAndDeBruijnTest do
  @moduledoc """
  Two things the Core did not agree with itself about.

  ## A hole is a Core node, except where it isn't

  `Kernel.check/3` accepts `{:hole, name}` at any type, and a definition mid-development
  legitimately contains one — only the release/emit boundary rejects holes. But `Term.term?/1`
  called it malformed, `Term.shift/3` and `Term.subst/3` had neither a clause nor a catch-all
  for it (so shifting any term containing a hole raised `FunctionClauseError`), and
  `to_external/from_external` could not round-trip it — contradicting `docs/KERNEL.md`'s claim
  that "every checked term has a total, reversible JSON-able encoding". A hole carries no de
  Bruijn variables, so it is an inert leaf exactly like `{:int_lit, _}`.

  `Kernel.infer/2` had no hole clause either, and raised. `{:absurd}` sitting two lines above
  it shows the right answer: fail cleanly rather than crash the kernel with an unmatched
  clause. A hole has nothing to infer — its type comes from the expected type, as in Agda and
  Idris — so it is an error, not an exception. `MetaCheck.progresses?/2` and
  `type_preserved?/2` both dispatch on `infer/2`'s result with a `case`/`else` that cannot
  catch a raise, and crashed on a legitimate term.

  ## A negative de Bruijn index is not a variable

  `Term.term?/1` has always rejected `{:var, -1}`. `Context.lookup/2` and `Eval.eval/2` both
  reached it through `Enum.at/2`, which counts from the END for a negative index — so
  `lookup(ctx, -1)` returned the OLDEST binding's type and the trusted kernel reported
  `{:var, -1}` as well-typed at a binding it does not name. Both now reject it.

  An index past the end of the environment is a different matter and stays a rigid free
  variable: Core admits open terms, `Conv.conv?/5` compares the neutrals both sides evaluate
  to, and `Antigen.Generators.ConvPair` pins the behaviour with its own coverage cell. The
  wrinkle worth knowing is that `{:nvar, l}` is a de Bruijn LEVEL and that arm reuses the
  index as one; it is coherent only while the value is not read back, since `Quote.reify/2`
  would turn it into the negative index `depth - k - 1`. Callers that reify supply
  `Context.env/1`, which binds every index in scope.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Kernel, MetaCheck, Term}

  describe "a hole is an inert Core leaf" do
    test "term? recognises it" do
      assert Term.term?({:hole, "body"})
      refute Term.term?({:hole, :not_a_string})
    end

    test "term? recognises {:absurd} too — same omission, same live node" do
      assert Term.term?({:absurd})
    end

    test "shift is the identity on it, at any amount and cutoff" do
      assert Term.shift({:hole, "p"}, 1, 0) == {:hole, "p"}
      assert Term.shift({:hole, "p"}, 3, 5) == {:hole, "p"}
    end

    test "shift descends through :app and :case into a nested hole without crashing" do
      branch = {:reflexive, 1, {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:var, 0}}}
      term = {:app, {:case, {:hole, "p"}, {:type, 0}, [branch]}, {:int_lit, 0}}

      assert Term.shift(term, 1, 0) == term
    end

    test "subst is the identity on it" do
      assert Term.subst({:hole, "p"}, 0, {:int_lit, 5}) == {:hole, "p"}
    end

    test "to_external/from_external round-trip it" do
      assert Term.from_external(Term.to_external({:hole, "body"})) == {:hole, "body"}
    end

    test "infer fails cleanly rather than raising an unmatched clause" do
      assert Kernel.infer(Context.empty(), {:hole, "x"}) == {:error, {:hole_in_inference_position, "x"}}
    end

    test "MetaCheck.progresses?/2 reports false on a hole instead of crashing" do
      assert MetaCheck.progresses?(Context.empty(), {:hole, "x"}) == false
    end
  end

  describe "negative de Bruijn indices" do
    setup do
      ctx = Context.empty() |> Context.extend({:vint_type}) |> Context.extend({:vtype, 0})
      {:ok, ctx: ctx}
    end

    test "term? rejects one" do
      refute Term.term?({:var, -1})
    end

    test "lookup fails on a negative index, like an out-of-range one", %{ctx: ctx} do
      assert Context.lookup(ctx, 0) == {:vtype, 0}
      assert Context.lookup(ctx, 1) == {:vint_type}
      assert Context.lookup(ctx, 2) == nil
      assert Context.lookup(ctx, -1) == nil
    end

    test "the kernel refuses to type one instead of borrowing the oldest binding", %{ctx: ctx} do
      assert Kernel.infer(ctx, {:var, -1}) == {:error, {:unbound_var, -1}}
    end

    test "eval raises rather than returning the oldest binding's value" do
      assert_raise RuntimeError, ~r/negative de Bruijn index/, fn ->
        Eval.eval({:var, -1}, [{:vint_type}, {:vtype, 0}])
      end
    end

    test "an index past the end of the environment is still a rigid free variable" do
      assert Eval.eval({:var, 0}, []) == {:vneutral, {:nvar, 0}}
      assert Eval.eval({:var, 5}, [{:vint_type}]) == {:vneutral, {:nvar, 5}}
    end
  end
end
