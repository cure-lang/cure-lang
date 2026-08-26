defmodule Cure.Core.ValueTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Value

  test "recognises each value shape" do
    cl = {:closure, [], {:var, 0}}
    assert Value.value?({:vtype, 0})
    assert Value.value?({:vpi, Cure.Core.Grade.unrestricted(), {:vtype, 0}, cl})
    assert Value.value?({:vlam, Cure.Core.Grade.unrestricted(), {:vtype, 0}, cl})
    assert Value.value?({:vneutral, {:nvar, 0}})
    # Inductive Sigma (D2): the dependent pair value is an ordinary `{:vdata,
    # :Sigma}` former and `{:vctor, :mk_pair}` intro — the `{:vdata}`/`{:vctor}`
    # rows below cover it; no `{:vsigma}`/`{:vpair}` value shapes remain.
    assert Value.value?({:vdata, :Sigma, [{:vtype, 0}, {:vlam, Cure.Core.Grade.unrestricted(), {:vtype, 0}, cl}]})
    assert Value.value?({:vctor, :mk_pair, [{:vtype, 0}, {:vtype, 1}]})
    assert Value.value?({:vdata, :SF, [{:vtype, 0}]})
    assert Value.value?({:vctor, :seq, [{:vtype, 0}]})
    refute Value.value?({:vtype, 3})
    refute Value.value?(:nope)
  end

  test "recognises each neutral shape" do
    assert Value.neutral?({:nvar, 0})
    assert Value.neutral?({:nglobal, :and})
    assert Value.neutral?({:napp, {:nvar, 0}, {:vtype, 0}})
    # Inductive Sigma (D2): a stuck projection is a stuck `{:ncase}` over the
    # neutral pair (covered by the `{:ncase}` row below) — no `{:nfst}`/`{:nsnd}`.

    assert Value.neutral?({:ncase, {:nvar, 0}, {:closure, [], {:type, 0}}, [{:prim, 0, {:closure, [], {:type, 0}}}]})

    refute Value.neutral?({:nvar, -1})
    refute Value.neutral?(:nope)
    # {:nprim} retired (K2, spec 2026-07-09): a stuck arithmetic op is a stuck
    # `{:napp}` spine over the builtin-op global — no bespoke neutral remains.
    refute Value.neutral?({:nprim, :add, [{:vint, 1}, {:vint, 2}]})
  end

  test "a closure carries an env (list of values) and a term" do
    assert Value.closure?({:closure, [], {:var, 0}})
    assert Value.closure?({:closure, [{:vtype, 0}], {:var, 0}})
    refute Value.closure?({:closure, :not_a_list, {:var, 0}})
    refute Value.closure?({:closure, [], :not_a_term})
  end
end
