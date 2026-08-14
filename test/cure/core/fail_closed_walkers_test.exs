defmodule Cure.Core.FailClosedWalkersTest do
  @moduledoc """
  Two TCB defects with one shape: state that leaks out of a dynamic scope, and walkers that
  answer "nothing here" for a node they do not recognize.

  ## Fuel is a dynamically-scoped variable

  `Normalise.with_fuel/2` keeps the budget in the process dictionary and used to
  `Process.delete` the key unconditionally on exit. A nested fueled call — `Conv.conv_within?/6`
  inside a fueled `nf/3`, or a reentrant `whnf/3` — therefore wiped the enclosing, still-live
  counter on its way out, and every δ-unfold after it in the outer computation found no key
  and ran unbounded. The bound a caller asked for silently stopped being a bound. It now
  saves and restores, the way any dynamically-scoped variable must.

  ## Walkers over an open term representation must fail closed

  `Certificate.calls?/2` and `Certificate.walk_node/4`, and `TotalityClosure.collect/1`, are
  hand-enumerated case-lists over the Core grammar with catch-alls that fail OPEN —
  `do: false`, `do: acc`, `do: []`. An unrecognized tuple contributed "no call here" rather
  than "unknown, be conservative". That is the opposite convention from the rest of the same
  directory: `Term.term?/1` answers `false` for an unrecognized node, and
  `Validator.children/1` is explicitly documented as descending conservatively "so a
  forbidden node buried in an unknown wrapper cannot escape the walker (fail-closed)".

  The consequences are unsoundness, not incompleteness. `calls?/2` is the fast path that
  decides whether size-change analysis runs *at all*: a false `false` certifies a function
  nobody ever analysed, and the kernel will then δ-unfold something that may not terminate.
  `TotalityClosure.collect/1` decides which globals get submitted for certification, and §7's
  `:totality_required` gate rests entirely on that closure being complete.

  Idris's `Core/Termination/SizeChange.idr`, which `certificate.ex` ports, walks a closed
  `CExp` grammar and cannot have this gap. Cure's Core is open tuples, so the walkers have to
  earn what Idris gets from its datatype.

  `:rewrite` is a live node today, so the `TotalityClosure` hole was reachable — and
  `Antigen.Assays.TotalityClosureAssay`'s "independent" completeness oracle was a verbatim
  copy of the same walker, missing the same clause. Both sides of that property shared one
  blind spot, so it could never fail. It is fixed here too.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Inductive, Normalise}
  alias Cure.Elab.TotalityClosure

  describe "nested fuel scopes" do
    test "a nested with_fuel restores the enclosing counter instead of deleting it" do
      key = Normalise.fuel_key()
      Process.put(key, 7)

      assert :inner_done == Normalise.with_fuel(3, fn -> :inner_done end)
      assert Process.get(key) == 7
    after
      Process.delete(Normalise.fuel_key())
    end

    test "a nested conv_within? leaves the enclosing budget intact" do
      remaining =
        Normalise.with_fuel(5, fn ->
          assert {:ok, true} = Conv.conv_within?({:type, 0}, {:type, 0}, [], 0, nil, 1)
          Process.get(Normalise.fuel_key())
        end)

      assert remaining == 5
    end

    test "a reentrant whnf does not let the outer budget run unbounded" do
      # `:one_step`'s body is a closed literal, so each δ-unfold costs exactly one unit.
      env = Env.empty() |> Env.add_def(:one_step, {:int_type}, {:int_lit, 99}) |> Env.certify(:one_step)
      ctx = Context.empty(env)

      result =
        Normalise.with_fuel(2, fn ->
          assert {:int_lit, 99} == Normalise.whnf(ctx, {:global, :one_step}, fuel: 1)

          # The outer scope still holds its full 2 units. Three more unfolds must exhaust.
          for _ <- 1..3 do
            Normalise.whnf_value({:vneutral, {:nglobal, :one_step}}, env, delta: :certified)
          end

          :outer_survived_without_exhaustion
        end)

      assert result == :fuel_exhausted
    end
  end

  describe "termination analysis descends into unrecognized nodes" do
    @ty {:pi, Cure.Core.Grade.unrestricted(), {:type, 0}, {:type, 0}}

    test "a self-call hidden inside an unrecognized wrapper is not certified total" do
      # f(n) = <wrap>(f(n)) — literally `f = f` with one extra tuple layer. No argument is
      # ever threaded through the self-call, so this diverges under any evaluator.
      body = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:audit_wrap, {:app, {:global, :f}, {:var, 0}}}}
      env = Env.empty() |> Env.add_def(:f, @ty, body)

      refute Cure.Test.TotalityCertificateHelper.provably_total?(env, :f)
    end

    test "a self-call hidden inside a live :rewrite node is not certified total" do
      dom = {:type, 0}
      body = {:lam, Cure.Core.Grade.unrestricted(), dom, {:rewrite, dom, dom, {:app, {:global, :loop}, {:var, 0}}}}

      env = Env.add_def(Env.empty(), :loop, @ty, body)
      refute Cure.Test.TotalityCertificateHelper.provably_total?(env, :loop)
    end

    test "a mutual cycle with one leg hidden inside a wrapper is not certified total" do
      # f(x) = <wrap>(g(x)); g(x) = f(x). `x` never changes. Unwrapped, this is already
      # rejected. Hiding f's call to g used to starve the endo-edge check of every edge,
      # so `Enum.all?/2` passed vacuously.
      f_body = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:audit_wrap, {:app, {:global, :g}, {:var, 0}}}}
      g_body = {:lam, Cure.Core.Grade.unrestricted(), {:type, 0}, {:app, {:global, :f}, {:var, 0}}}
      env = Env.empty() |> Env.add_def(:f, @ty, f_body) |> Env.add_def(:g, @ty, g_body)

      refute Cure.Test.TotalityCertificateHelper.provably_total?(env, :f)
    end

    test "a genuinely decreasing function is still certified" do
      # Guard against a fail-closed walker that simply rejects everything.
      nat = {:data, :Nat, [], []}

      env =
        Env.empty()
        |> Inductive.declare(Inductive.family(:Nat, [], [], 0), [
          Inductive.ctor(:Z, [], []),
          Inductive.ctor(:S, [{:n, nat}], [])
        ])

      # id(n) = case n of Z -> Z | S k -> S k   (no recursion at all)
      body =
        {:lam, Cure.Core.Grade.unrestricted(), nat,
         {:case, {:var, 0}, nat, [{:Z, 0, {:ctor, :Z, []}}, {:S, 1, {:ctor, :S, [{:var, 0}]}}]}}

      env = Env.add_def(env, :id, {:pi, Cure.Core.Grade.unrestricted(), nat, nat}, body)
      assert Cure.Test.TotalityCertificateHelper.provably_total?(env, :id)
    end
  end

  describe "type-level reachability descends into unrecognized nodes" do
    test "a global reachable only through a :rewrite node enters the type-level closure" do
      dec = {:data, :Dec, [], []}

      outer_body =
        {:lam, Cure.Core.Grade.unrestricted(), dec, {:rewrite, dec, dec, {:app, {:global, :inner}, {:var, 0}}}}

      env =
        Env.empty()
        |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [Inductive.ctor(:Dcoupled, [], [])])
        |> Env.add_def(:outer, {:pi, Cure.Core.Grade.unrestricted(), dec, dec}, outer_body)
        |> Env.add_def(
          :inner,
          {:pi, Cure.Core.Grade.unrestricted(), dec, dec},
          {:lam, Cure.Core.Grade.unrestricted(), dec, {:var, 0}}
        )
        |> Inductive.declare(Inductive.family(:Wrap, [], [{:d, dec}], 0), [
          Inductive.ctor(:mkWrap, [{:x, dec}], [{:app, {:global, :outer}, {:var, 0}}])
        ])

      assert MapSet.member?(TotalityClosure.type_level_fns(env), :inner)
    end

    test "the Antigen completeness oracle sees it too — it must not share the subject's blind spot" do
      dec = {:data, :Dec, [], []}

      outer_body =
        {:lam, Cure.Core.Grade.unrestricted(), dec, {:rewrite, dec, dec, {:app, {:global, :inner}, {:var, 0}}}}

      env =
        Env.empty()
        |> Inductive.declare(Inductive.family(:Dec, [], [], 0), [Inductive.ctor(:Dcoupled, [], [])])
        |> Env.add_def(:outer, {:pi, Cure.Core.Grade.unrestricted(), dec, dec}, outer_body)
        |> Env.add_def(
          :inner,
          {:pi, Cure.Core.Grade.unrestricted(), dec, dec},
          {:lam, Cure.Core.Grade.unrestricted(), dec, {:var, 0}}
        )
        |> Inductive.declare(Inductive.family(:Wrap, [], [{:d, dec}], 0), [
          Inductive.ctor(:mkWrap, [{:x, dec}], [{:app, {:global, :outer}, {:var, 0}}])
        ])

      assert MapSet.member?(Antigen.Assays.TotalityClosureAssay.__reachable__(env), :inner)
    end
  end
end
