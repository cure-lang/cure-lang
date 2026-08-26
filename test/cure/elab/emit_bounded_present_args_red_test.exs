defmodule Cure.Elab.EmitBoundedPresentArgsRedTest do
  @moduledoc """
  FINDING D (erasure-unify cluster): `Cure.Elab.Emit`'s private
  `bounded_present_args/3` (lib/cure/elab/emit.ex:1176) re-DERIVES which
  constructor arguments are runtime-present by comparing `length(args)` against
  the ctor's declared quantity count, and — when that length happens to match —
  RE-FILTERS with the same raw `:unrestricted` literal check as FINDING C,
  instead of trusting the erasure `Erase.erase/2` already performed (or, short
  of that, using `Grade.present?/1`).

  The audit notes this length-guess is a no-op for the only family CURRENTLY
  routed through it (the canonical `Std.Bounded`, whose sole present field is
  always preceded by an erased index, so the lengths can never coincide). This
  test shows the guess is very much LIVE and WRONG the moment ANYTHING is
  registered under the `:bounded` builtin key with a constructor whose single
  field is `:linear` (present, per `Grade.present?/1`) rather than
  `:unrestricted`: erasure correctly keeps the field (length(args) ends up
  EQUAL to length(quantities), since nothing was dropped), which trips the
  buggy re-filter branch, whose raw `:unrestricted` match discards the
  `:linear` field anyway — silently corrupting the value to the `First`-style
  zero-arg encoding (BEAM integer `0`) no matter what was actually
  constructed.

  Built directly against `Cure.Core.Inductive`/`Cure.Elab.Emit` (bypassing
  surface syntax, which cannot yet declare a `:linear` constructor field — see
  MEMORY "QTT grades progress"), exactly like FINDING C's fixture.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Grade, Inductive}
  alias Cure.Elab.Emit

  test "@linear a :-graded single-field ctor routed through the Bounded path keeps its value" do
    dummy_type = {:type, 0}

    # A single constructor, `Nxt`, whose one field is `:linear` (present).
    ctor = Inductive.ctor(:Nxt, [{:v, dummy_type}], [], [:linear], [])
    family = Inductive.family(:Foo3, [], [], 0)

    env =
      Env.empty()
      |> Inductive.declare(family, [ctor])
      |> Inductive.register_builtin(:bounded, :Foo3)

    foo3_type = {:data, :Foo3, [], []}

    mk_type = {:pi, Grade.unrestricted(), dummy_type, foo3_type}
    mk_body = {:lam, Grade.unrestricted(), dummy_type, {:ctor, :Nxt, [{:var, 0}]}}

    env = Env.add_def(env, :mk, mk_type, mk_body, [Grade.unrestricted()])

    assert {:ok, mod} =
             Emit.compile_and_load(env, module: Cure.Elab.EmitBoundedPresentArgsRedFixture, functions: [:mk])

    # DESIRED POST-FIX BEHAVIOR: `Grade.present?(:linear)` is `true`, so the
    # field must survive intact through the Bounded-style ctor encoding
    # (`Next`-analogue: present field `n` -> `n + 1`), exactly as an
    # `:unrestricted` field would. `mk(999)` must recover `999 + 1 = 1000`, NOT
    # silently collapse to the zero-argument (`First`-analogue) encoding `0`.
    assert mod.mk(999) == 1000
  end
end
