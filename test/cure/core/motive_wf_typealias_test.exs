defmodule Cure.Core.MotiveWfTypealiasTest do
  @moduledoc """
  A `case`/`match` whose result type is a bare typealias global — e.g. a motive
  `λ(_ : Foo). String` where `String : Type := List(Char)` — must be ACCEPTED.

  `check_motive_wf` sorts the motive body with `infer_type_value_sort`, which had
  clauses for `{:nvar, _}` and `{:napp, _, _}` neutrals but NONE for a bare
  `{:nglobal, _}`. So a typealias standing in type position fell through to
  `{:error, :bad_motive}` — spuriously rejecting every `match … -> String` and
  every abstract interface method returning an aliased type (`Std.Show`,
  `Std.Io`). The added `{:nglobal, _}` clause mirrors the `{:napp}` one: reify the
  neutral and `infer` it, admitting the motive only when the kernel's own
  judgement says the reified `{:global, g}` is a type (`{:vtype, l}`). It trusts
  nothing from the elaborator — a global standing for a VALUE (non-type) is still
  rejected.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Context, Env, Grade, Inductive, Kernel}

  # An inductive `Foo` with one nullary ctor, plus:
  #   AliasFoo : Type := Foo      (a typealias — a global standing for a TYPE)
  #   notType  : Foo  := foo      (a global standing for a VALUE, NOT a type)
  defp ctx do
    foo = {:data, :Foo, [], []}

    env =
      Env.empty()
      |> Inductive.declare(Inductive.family(:Foo, [], [], 0), [Inductive.ctor(:foo, [], [])])
      |> Env.add_def(:AliasFoo, {:type, 0}, foo)
      |> Env.certify(:AliasFoo)
      |> Env.add_def(:notType, foo, {:ctor, :foo, []})
      |> Env.certify(:notType)

    Context.empty(env)
  end

  test "a constant motive whose body is a typealias global is accepted" do
    foo = {:data, :Foo, [], []}
    # motive λ(_ : Foo). AliasFoo — body is the neutral global {:nglobal, :AliasFoo}.
    # The branch must inhabit the result type AliasFoo, which δ-unfolds to Foo, so
    # {:ctor, :foo, []} : Foo ≈ AliasFoo.
    motive = {:lam, Grade.unrestricted(), foo, {:global, :AliasFoo}}
    node = {:case, {:ctor, :foo, []}, motive, [{:foo, 0, {:ctor, :foo, []}}]}
    assert {:ok, _} = Kernel.infer(ctx(), node)
  end

  test "a motive whose body is a VALUE global (non-type) is still rejected" do
    foo = {:data, :Foo, [], []}
    # motive λ(_ : Foo). notType — notType : Foo is a value, not a type. The
    # {:nglobal} clause reifies + infers and gets Foo (not {:vtype, _}), so the
    # motive is refused. Guards the fix against admitting non-types.
    motive = {:lam, Grade.unrestricted(), foo, {:global, :notType}}
    node = {:case, {:ctor, :foo, []}, motive, [{:foo, 0, {:ctor, :foo, []}}]}
    assert {:error, :bad_motive} = Kernel.infer(ctx(), node)
  end
end
