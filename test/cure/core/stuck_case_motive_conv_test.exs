defmodule Cure.Core.StuckCaseMotiveConvTest do
  @moduledoc """
  A stuck `case` (`{:ncase, …}`) stores its motive as a COMPLETE function term
  in a closure — `quote.ex`'s `instantiate` evaluates it with NO extra binder.
  Conversion must instantiate it the same way. The old `conv_neutral?` ncase arm
  compared the two motive closures with `conv_closure?`, which pushes a spurious
  fresh binder; that shift makes a motive that references its captured
  environment read the fresh binder instead — so two ncases whose motives CAPTURE
  DIFFERENT VALUES were declared convertible. That is an unsound false-accept.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Conv

  # A closed constructor type placeholder for the motive's domain (never forced).
  @foo_type {:vdata, :Foo, []}

  # motive λ(_ : Foo). <captured var 0> — the body references the closure's
  # captured environment (de Bruijn 1 = index 0 of env, under the λ binder).
  @motive_term {:lam, Cure.Core.Grade.unrestricted(), {:data, :Foo, [], []}, {:var, 1}}

  defp ncase_with_capture(captured) do
    motive_cl = {:closure, [captured], @motive_term}
    # one branch for a nullary ctor `foo`, trivial body (its own de Bruijn 0 slot
    # is never reached because the scrutinee stays neutral).
    branches = [{:foo, 0, {:closure, [captured], {:type, 0}}}]
    {:vneutral, {:ncase, {:nvar, 0}, motive_cl, branches}}
  end

  test "ncases whose motives capture DIFFERENT values are NOT convertible" do
    p1 = {:vneutral, {:nvar, 1}}
    p2 = {:vneutral, {:nvar, 2}}
    v1 = ncase_with_capture(p1)
    v2 = ncase_with_capture(p2)

    refute Conv.conv_values?(v1, v2, 3),
           "motives return different captured values (#{inspect(@foo_type)}); must reject"
  end

  test "an ncase is convertible with itself (reflexivity preserved)" do
    p = {:vneutral, {:nvar, 1}}
    v = ncase_with_capture(p)
    assert Conv.conv_values?(v, v, 3)
  end
end
