defmodule Cure.Core.MotiveWfEffectTest do
  @moduledoc """
  A `case`/`match` whose result type is `Effect(T)` — e.g. a motive
  `λ(_ : Foo). Effect(Foo)` — must be ACCEPTED.

  `check_motive_wf` sorts the motive body with `infer_type_value_sort`, which had
  clauses for `{:vtype}`, the neutrals, the primitives, `{:vdata}` and `{:vpi}` but
  NONE for `{:veffect_type, _}`. So a motive body that is a direct `Effect(T)` fell
  through to the catch-all → `:not_a_type_value` → a spurious `{:error, :bad_motive}`
  — even though `infer/2`'s own formation rule (`Effect : Type ℓ → Type ℓ`) types the
  very same TERM without complaint. A false negative, not unsoundness.

  This is what forced every transparent OTP callback in `lib/std/{actor,fsm,app}.cure`
  to launder its result type through a `typealias EventResult = Effect(...)`: an alias
  makes the motive body a `{:nglobal}` neutral, which the typealias clause already
  admitted. Those aliases were a kernel-facing dodge, never an abstraction.

  The added clause mirrors the formation rule exactly — `Effect(t)` sorts at `t`'s own
  level — and recurses on the sub-VALUE rather than reifying and re-inferring, for the
  same reason the `{:vpi}` clause does (see the indexed-payload test below).
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Grade, Inductive, Kernel}

  @foo {:data, :Foo, [], []}
  @dec {:data, :Dec, [], []}

  # Foo: one nullary ctor. Plus `notType : Foo := foo` — a global standing for a
  # VALUE, not a type. It is the payload in the negative control.
  defp ctx do
    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:foo, [], [])])
      |> Env.add_def(:notType, @foo, {:ctor, :foo, []})
      |> Env.certify(:notType)

    Context.empty(env)
  end

  # POSITIVE: motive `λ(_ : Foo). Effect(Foo)`. Body value is `{:veffect_type, …}`,
  # which had no sorter clause. The branch inhabits it with `pure(foo) : Effect(Foo)`.
  test "a constant motive whose body is Effect(T) is accepted (was :bad_motive)" do
    motive = {:lam, Grade.unrestricted(), @foo, {:effect_type, @foo}}
    node = {:case, {:ctor, :foo, []}, motive, [{:foo, 0, {:effect_pure, {:ctor, :foo, []}}}]}

    assert {:ok, _} = Kernel.infer(ctx(), node)
  end

  # NEGATIVE CONTROL: motive `λ(_ : Foo). Effect(notType)`. `notType` is a value, so
  # `Effect(notType)` is not a type and the motive must still be refused. Rejected both
  # before and after the fix — it proves the new clause is a real sort check on the
  # payload, not a blanket accept of anything wearing an `Effect` head.
  test "a motive whose body is Effect(<value global>) is still rejected (:bad_motive)" do
    motive = {:lam, Grade.unrestricted(), @foo, {:effect_type, {:global, :notType}}}
    node = {:case, {:ctor, :foo, []}, motive, [{:foo, 0, {:effect_pure, {:ctor, :foo, []}}}]}

    assert {:error, :bad_motive} = Kernel.infer(ctx(), node)
  end

  # Dec: two nullary ctors. SNat(d : Dec): an INDEXED family with one ctor per index.
  defp indexed_env do
    Env.empty()
    |> Inductive.declare(
      Inductive.family(:Dec, [], [], 0),
      [Inductive.ctor(:Dcoupled, [], []), Inductive.ctor(:Causal, [], [])]
    )
    |> Inductive.declare(
      Inductive.family(:SNat, [], [{:d, @dec}], 0),
      [
        Inductive.ctor(:snat0, [], [{:ctor, :Dcoupled, []}]),
        Inductive.ctor(:snat1, [], [{:ctor, :Causal, []}])
      ]
    )
  end

  # POSITIVE, and it pins the IMPLEMENTATION, not just the behaviour: motive
  # `λs. Effect(SNat s)` — an INDEXED family under the `Effect` head. `Quote.reify`
  # collapses `{:vdata, name, args}` → `{:data, name, args, []}` (it has no inductive
  # signature to recover the param/index split), so a sorter clause implemented as
  # reify-then-re-infer would fail this with `:arg_arity` → a false `:bad_motive`,
  # exactly as the Π-domain case did before the `{:vpi}` clause switched to value
  # recursion. Recursing on the sub-VALUE bottoms out in the `{:vdata,…}` clause and
  # reads the family's declared level with no lossy round-trip.
  test "an INDEXED family under Effect sorts (pins value-recursion over reify)" do
    snat_s = {:data, :SNat, [], [{:var, 0}]}
    motive = {:lam, Grade.unrestricted(), @dec, {:effect_type, snat_s}}
    def_type = {:pi, Grade.unrestricted(), @dec, {:effect_type, snat_s}}

    body =
      {:lam, Grade.unrestricted(), @dec,
       {:case, {:var, 0}, motive,
        [
          {:Dcoupled, 0, {:effect_pure, {:ctor, :snat0, []}}},
          {:Causal, 0, {:effect_pure, {:ctor, :snat1, []}}}
        ]}}

    env = Env.add_def(indexed_env(), :probe, def_type, body)

    assert :ok == Kernel.check_def(env, :probe)
  end
end
