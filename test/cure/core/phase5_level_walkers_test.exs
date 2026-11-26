defmodule Cure.Core.Phase5LevelWalkersTest do
  @moduledoc """
  Adversarial U2 structural/E-layer walker tests, not kernel typing judgments.

  Raw normal-form structs are intentional: malformed atoms must be observed
  before a constructor can normalize, serialize, or erase the evidence.
  """
  use ExUnit.Case, async: false

  alias Cure.Audit.Refs
  alias Cure.Core.{Env, Eval, Serialize, Sort, Term, UniverseLevel, Validator}
  alias Cure.Elab.{Erase, MetaCtx, Relevance, Subst, Unify, UniverseTraversal}
  alias Cure.Core.UniverseLevel, as: L

  @kinds [:finite_sort, :level_value]
  @grades [:erased, :linear, :affine, :unrestricted]

  test "Core level and sort mapping flatten known replacements and preserve limit indices" do
    source = L.max(L.succ(L.succ(L.atom({:var, 0}))), L.succ(L.atom({:var, 1})))

    transform = fn
      {:var, 0} -> {:level_value, L.closed(37)}
      {:var, 1} -> {:var, 0}
    end

    expected = L.max(L.closed(39), L.succ(L.atom({:var, 0})))
    assert L.map(source, transform) == expected
    assert Sort.map({:finite, source}, transform) == {:finite, expected}
    assert Sort.map({:omega, 37}, fn _ -> flunk("a limit sort has no finite atoms") end) == {:omega, 37}
    assert :ok = L.validate(expected, nil)
  end

  test "raw atom projection preserves forbidden evidence even with malformed offsets" do
    for kind <- @kinds, offset <- [-1, :malformed] do
      hole = {:hole, "hidden-level-hole"}
      struct_payload = %UniverseLevel{constant: 0, atoms: [{hole, offset}]}
      tagged_payload = {:level_nf, 0, [{hole, offset}]}

      for payload <- [struct_payload, tagged_payload] do
        term = wrap(kind, payload)
        assert Term.level_atoms(term) == [hole]
        assert Erase.has_hole?(term)
        assert %{holes: ["hidden-level-hole"]} = Refs.scan(term)
        assert hole in Validator.nodes(term)
        refute Term.term?(term)
      end
    end
  end

  test "metas inside neutral atoms retain the ambient frame at Pi lambda let and case sites" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new(), {:level_type})
    assert {:ok, solved} = Unify.unify({:meta, id}, {:var, 0}, ctx)

    for kind <- @kinds, grade <- @grades do
      pending = raw(kind, {:app, {:global, :"Phase5#level_function"}, {:meta, id}})
      ambient = raw(kind, {:app, {:global, :"Phase5#level_function"}, {:var, 0}})
      lifted = raw(kind, {:app, {:global, :"Phase5#level_function"}, {:var, 1}})

      for binder <- [:lam, :pi] do
        assert Unify.zonk({binder, grade, pending, pending}, solved) ==
                 {binder, grade, ambient, lifted}
      end

      assert Unify.zonk({:let, grade, pending, pending, pending}, solved) ==
               {:let, grade, ambient, ambient, lifted}

      term = {:case, pending, pending, [{:C, 2, pending}]}
      branch = raw(kind, {:app, {:global, :"Phase5#level_function"}, {:var, 2}})
      assert Unify.zonk(term, solved) == {:case, ambient, ambient, [{:C, 2, branch}]}
    end
  end

  test "alternating level containers lift ambient metas through a five-binder stack preserving grades" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new(), {:level_type})
    assert {:ok, solved} = Unify.unify({:meta, id}, {:var, 0}, ctx)

    for outer <- @kinds, inner <- @kinds, grade <- @grades do
      pending = nested(outer, inner, {:app, {:global, :"Phase5#level_function"}, {:meta, id}})
      lifted = nested(outer, inner, {:app, {:global, :"Phase5#level_function"}, {:var, 5}})

      term =
        {:lam, grade, {:int_type},
         {:let, grade, {:int_type}, {:int_lit, 7},
          {:case, {:global, :"Phase5#scrutinee"}, {:level_type}, [{:C, 2, {:pi, grade, {:int_type}, pending}}]}}}

      expected =
        {:lam, grade, {:int_type},
         {:let, grade, {:int_type}, {:int_lit, 7},
          {:case, {:global, :"Phase5#scrutinee"}, {:level_type}, [{:C, 2, {:pi, grade, {:int_type}, lifted}}]}}}

      assert Unify.zonk(term, solved) == expected
      assert binder_grades(expected) == [grade, grade, grade]
    end
  end

  test "zonking a solution obtained under a binder restores its ambient open level without capture" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new(), {:level_type})

    for outer <- @kinds, inner <- @kinds, binder <- [:lam, :pi] do
      lhs = {binder, :erased, {:level_type}, {:meta, id}}
      rhs = {binder, :erased, {:level_type}, nested(outer, inner, {:var, 1})}
      assert {:ok, solved} = Unify.unify(lhs, rhs, ctx)
      assert MetaCtx.solution(solved, id) == nested(outer, inner, {:var, 0})
      assert Unify.zonk(lhs, solved) == rhs
    end
  end

  test "zonking lifts ambient open level solutions through every case field binder" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new(), {:level_type})

    for outer <- @kinds, inner <- @kinds do
      assert {:ok, solved} = Unify.unify({:meta, id}, nested(outer, inner, {:var, 0}), ctx)

      term =
        {:case, {:global, :"Phase5#scrutinee"}, {:level_type}, [{:C, 2, {:meta, id}}]}

      expected =
        {:case, {:global, :"Phase5#scrutinee"}, {:level_type}, [{:C, 2, nested(outer, inner, {:var, 2})}]}

      assert Unify.zonk(term, solved) == expected
    end
  end

  test "holes remain visible through both sorts of nested level containers" do
    for outer <- @kinds, inner <- @kinds do
      hole = {:hole, "nested-level-hole"}
      term = nested(outer, inner, hole)
      assert Erase.has_hole?(term)
      assert %{holes: ["nested-level-hole"]} = Refs.scan(term)
      assert hole in Validator.nodes(term)

      assert {:error, diagnostics} = Validator.validate(term, %{no_hole: :reject, level_expr: :reject})
      assert Enum.any?(diagnostics, &(&1.clause == :no_hole and &1.node == hole))
      assert Enum.any?(diagnostics, &(&1.clause == :level_expr))
      refute Term.term?(term)
    end
  end

  test "audit finds globals hidden in nested levels and case branches" do
    for outer <- @kinds, inner <- @kinds do
      hidden = {:global, :"Phase5#hidden_level_provider"}
      branch = {:case, {:global, :"Phase5#scrutinee"}, {:level_type}, [{:C, 2, raw(inner, hidden)}]}
      term = raw(outer, branch)

      assert Refs.globals(term) == Enum.sort([:"Phase5#hidden_level_provider", :"Phase5#scrutinee"])
      assert hidden in Validator.nodes(term)
      refute Erase.has_hole?(term)
    end
  end

  test "metas are detected and refused at Core boundaries through nested levels" do
    for outer <- @kinds, inner <- @kinds do
      term = nested(outer, inner, {:meta, 91})
      assert Unify.has_meta?(term)
      refute Term.term?(term)
      assert_raise ArgumentError, fn -> Serialize.encode(term) end
      assert_raise ArgumentError, fn -> Refs.scan(term) end

      assert {:error, diagnostics} = Validator.validate(term, %{level_expr: :reject})
      assert Enum.any?(diagnostics, &(&1.clause == :level_expr))
    end
  end

  test "meta-aware reconstruction defers canonicalization until all atom metas are solved" do
    pending = %UniverseLevel{constant: 5, atoms: [{{:meta, 0}, 2}, {{:meta, 1}, 3}]}
    assert UniverseTraversal.map_level(pending, &Function.identity/1) == pending
    assert UniverseTraversal.map_sort({:finite, pending}, &Function.identity/1) == {:finite, pending}

    {ctx, first} = MetaCtx.fresh(MetaCtx.new(), {:level_type})
    {ctx, second} = MetaCtx.fresh(ctx, {:level_type})
    assert first == 0 and second == 1
    assert {:ok, ctx} = Unify.unify({:meta, first}, {:level_value, L.closed(37)}, ctx)
    assert {:ok, ctx} = Unify.unify({:meta, second}, {:level_value, L.closed(36)}, ctx)

    for kind <- @kinds do
      assert Unify.zonk(wrap(kind, pending), ctx) == wrap(kind, L.closed(39))
      refute Unify.has_meta?(Unify.zonk(wrap(kind, pending), ctx))
    end
  end

  test "zonking reaches solved metas through alternating level containers" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new(), {:level_type})
    assert {:ok, ctx} = Unify.unify({:meta, id}, {:level_value, L.closed(37)}, ctx)

    for outer <- @kinds, inner <- @kinds do
      term = nested(outer, inner, {:meta, id})
      expected_atom = {:app, {:global, :"Phase5#opaque"}, wrap(inner, L.closed(37))}
      zonked = Unify.zonk(term, ctx)
      assert zonked == wrap(outer, L.atom(expected_atom))
      refute Unify.has_meta?(zonked)
      assert Term.term?(zonked)
    end
  end

  test "occurs checking rejects a cycle hidden in either nested universe payload" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new(), {:level_type})

    for outer <- @kinds, inner <- @kinds do
      rhs = nested(outer, inner, {:meta, id})
      assert {:error, {:occurs_check, ^id, ^rhs}} = Unify.unify({:meta, id}, rhs, ctx)
      refute MetaCtx.solved?(ctx, id)
    end
  end

  test "scope escape is rejected under internal lambdas and Pis inside level atoms" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new(), {:level_type})

    for outer <- @kinds, inner <- @kinds, binder <- [:lam, :pi] do
      escaping = {binder, :erased, {:level_type}, nested(outer, inner, {:var, 1})}
      lhs = {:pi, :erased, {:level_type}, {:meta, id}}
      rhs = {:pi, :erased, {:level_type}, escaping}
      assert {:error, {:escaping_variable, ^id}} = Unify.unify(lhs, rhs, ctx)

      bound = {binder, :erased, {:level_type}, nested(outer, inner, {:var, 0})}
      assert {:ok, solved} = Unify.unify(lhs, {:pi, :erased, {:level_type}, bound}, ctx)
      assert MetaCtx.solution(solved, id) == bound
    end
  end

  test "case branch arity distinguishes local fields from escaping level atoms" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new(), {:level_type})
    lhs = {:lam, :erased, {:level_type}, {:meta, id}}

    for outer <- @kinds, inner <- @kinds do
      escaping =
        {:case, {:global, :"Phase5#scrutinee"}, {:level_type}, [{:C, 2, nested(outer, inner, {:var, 2})}]}

      assert {:error, {:escaping_variable, ^id}} =
               Unify.unify(lhs, {:lam, :erased, {:level_type}, escaping}, ctx)

      bound =
        {:case, {:global, :"Phase5#scrutinee"}, {:level_type}, [{:C, 2, nested(outer, inner, {:var, 1})}]}

      assert {:ok, solved} = Unify.unify(lhs, {:lam, :erased, {:level_type}, bound}, ctx)
      assert MetaCtx.solution(solved, id) == bound
    end
  end

  test "Subst and zonk preserve every original binder grade around universe payloads" do
    {ctx, id} = MetaCtx.fresh(MetaCtx.new(), {:level_type})
    assert {:ok, ctx} = Unify.unify({:meta, id}, {:level_value, L.closed(37)}, ctx)

    for kind <- @kinds, grade <- @grades do
      body = {:pi, grade, {:int_type}, raw(kind, {:meta, id})}
      term = {:lam, grade, {:int_type}, {:let, grade, {:int_type}, {:var, 1}, body}}
      assert binder_grades(Subst.shift(term, 2, 0)) == [grade, grade, grade]

      instantiated = Subst.instantiate(term, [{:int_lit, 7}])
      assert binder_grades(instantiated) == [grade, grade, grade]
      assert Unify.has_meta?(instantiated)

      zonked = Unify.zonk(instantiated, ctx)
      assert binder_grades(zonked) == [grade, grade, grade]
      refute Unify.has_meta?(zonked)
    end
  end

  test "Subst instantiation strengthens nested atoms without capturing case fields" do
    for outer <- @kinds, inner <- @kinds do
      term =
        {:case, {:global, :"Phase5#scrutinee"}, {:level_type}, [{:C, 2, nested(outer, inner, {:var, 2})}]}

      expected =
        {:case, {:global, :"Phase5#scrutinee"}, {:level_type}, [{:C, 2, nested(outer, inner, {:var, 3})}]}

      assert Subst.instantiate(term, [{:var, 1}]) == expected
    end
  end

  test "unresolved metas never enter Eval or serialization during meta-aware whnf" do
    for outer <- @kinds, inner <- @kinds do
      term = nested(outer, inner, {:meta, 29})
      ctx = MetaCtx.new()

      {result, entries} =
        trace_core_entries(fn -> Unify.whnf_meta_aware(term, ctx, Env.empty()) end)

      assert result == term
      assert Unify.has_meta?(result)
      assert Enum.any?(entries, fn {module, name, _args} -> module == Eval and name == :eval end)
      assert Enum.any?(entries, fn {module, _name, _args} -> module == Serialize end)
      refute Enum.any?(entries, fn {_module, _name, args} -> contains_meta?(args) end)
    end
  end

  test "unknown Core formers cannot pass substitution or reference-audit boundaries" do
    for kind <- @kinds,
        unknown <- [
          {:phase5_unknown_core, raw(kind, {:var, 0})},
          raw(kind, {:phase5_unknown_core, {:var, 0}})
        ] do
      refute Term.term?(unknown)
      assert_raise ArgumentError, fn -> Subst.shift(unknown, 1, 0) end
      assert_raise ArgumentError, fn -> Subst.instantiate(unknown, [{:int_lit, 7}]) end
      assert_raise ArgumentError, fn -> Refs.scan(unknown) end

      {ctx, id} = MetaCtx.fresh(MetaCtx.new())
      lhs = {:pi, :erased, {:level_type}, {:meta, id}}
      rhs = {:pi, :erased, {:level_type}, unknown}
      assert {:error, {:escaping_variable, ^id}} = Unify.unify(lhs, rhs, ctx)
    end
  end

  test "closed level constants are runtime-forbidden but erased variables in type positions remain allowed" do
    env = Env.empty()

    for constant <- [0, 37, 10 ** 40] do
      level = {:level_value, L.closed(constant)}

      assert {:error, {:runtime_relevant_level, :level_value, :returned}} =
               Relevance.check(env, :closed_level, [], level)

      assert {:error, {:runtime_relevant_level, :level_value, :present_arg}} =
               Relevance.check(env, :field_level, [], {:ctor, :unregistered, [level]})
    end

    type_domain = raw(:finite_sort, {:var, 0})
    term = {:lam, :unrestricted, type_domain, {:int_lit, 7}}
    assert :ok = Relevance.check(env, :erased_type_use, [:erased], term)
    assert :ok = Relevance.check(env, :ordinary_literal, [], {:int_lit, 0})
  end

  defp wrap(:finite_sort, payload), do: {:type, {:finite, payload}}
  defp wrap(:level_value, payload), do: {:level_value, payload}
  defp raw(kind, atom), do: wrap(kind, %UniverseLevel{constant: 0, atoms: [{atom, 0}]})
  defp nested(outer, inner, leaf), do: raw(outer, {:app, {:global, :"Phase5#opaque"}, raw(inner, leaf)})

  defp binder_grades({tag, grade, domain, body}) when tag in [:lam, :pi],
    do: [grade | binder_grades(domain) ++ binder_grades(body)]

  defp binder_grades({:let, grade, type, value, body}),
    do: [grade | binder_grades(type) ++ binder_grades(value) ++ binder_grades(body)]

  defp binder_grades(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.flat_map(&binder_grades/1)

  defp binder_grades(list) when is_list(list), do: Enum.flat_map(list, &binder_grades/1)
  defp binder_grades(%UniverseLevel{atoms: atoms}), do: binder_grades(atoms)
  defp binder_grades(_leaf), do: []

  defp contains_meta?({:meta, _}), do: true
  defp contains_meta?(tuple) when is_tuple(tuple), do: tuple |> Tuple.to_list() |> Enum.any?(&contains_meta?/1)
  defp contains_meta?(list) when is_list(list), do: Enum.any?(list, &contains_meta?/1)
  defp contains_meta?(map) when is_map(map), do: map |> Map.values() |> Enum.any?(&contains_meta?/1)
  defp contains_meta?(_leaf), do: false

  defp trace_core_entries(fun) do
    functions = [{Eval, :eval, 2}, {Serialize, :encode, 1}, {Serialize, :encode_node, 1}]
    tracer = spawn_link(fn -> collect_entries([]) end)

    for {module, _name, _arity} = function <- functions do
      Code.ensure_loaded!(module)
      assert :erlang.trace_pattern(function, true, [:local]) > 0
    end

    :erlang.trace(self(), true, [:call, {:tracer, tracer}])

    try do
      result = fun.()
      reference = :erlang.trace_delivered(self())

      receive do
        {:trace_delivered, _tracee, ^reference} -> :ok
      after
        5_000 -> flunk("Core-entry trace delivery timed out")
      end

      send(tracer, {:finish, self()})

      receive do
        {:entries, ^tracer, entries} -> {result, entries}
      after
        5_000 -> flunk("Core-entry trace collection timed out")
      end
    after
      :erlang.trace(self(), false, [:call])
      for function <- functions, do: :erlang.trace_pattern(function, false, [:local])
      send(tracer, :stop)
    end
  end

  defp collect_entries(entries) do
    receive do
      {:trace, _pid, :call, {module, name, arguments}} ->
        collect_entries([{module, name, arguments} | entries])

      {:finish, caller} ->
        send(caller, {:entries, self(), Enum.reverse(entries)})

      :stop ->
        :ok
    end
  end
end
