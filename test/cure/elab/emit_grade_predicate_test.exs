defmodule Cure.Elab.EmitGradePredicateTest do
  @moduledoc """
  A constructor field is present at runtime exactly when
  `Cure.Core.Grade.present?/1` says so — the same predicate
  `Cure.Elab.Erase.erase/2` uses to decide which constructor ARGUMENTS survive
  erasure. Emit's branch clauses have to agree with it, or a field kept at
  construction is dropped from the `case` pattern that reads it back out.

  Only `:erased` is absent, so `:linear` and `:affine` are the grades where a
  raw `q == :unrestricted` check disagrees with `Grade.present?/1`. Surface
  syntax does not yet spell a linear or affine constructor field, so this
  builds the family directly at the `Cure.Core.Inductive` level — unreachable
  from today's parser, live at the Core/Emit boundary for any hand-built Core
  term or future surface extension.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Grade, Inductive}
  alias Cure.Elab.Emit

  test "a `:linear`-graded constructor field survives to the runtime tuple and back" do
    # `Box` has exactly one constructor, `MkBox`, with a SINGLE field graded
    # `:linear`. Its type is value-level (`Int`, not `Type`) so both definitions
    # below are runtime definitions and actually reach the emitter.
    field_type = {:int_type}
    ctor = Inductive.ctor(:MkBox, [{:v, field_type}], [], [:linear], [])
    family = Inductive.family(:Box, [], [], 0)
    box_type = {:data, :Box, [], []}

    mk_type = {:pi, Grade.unrestricted(), field_type, box_type}
    mk_body = {:lam, Grade.unrestricted(), field_type, {:ctor, :MkBox, [{:var, 0}]}}

    # `access` cases on the single `MkBox` branch and returns its one field.
    access_type = {:pi, Grade.unrestricted(), box_type, field_type}

    access_body =
      {:lam, Grade.unrestricted(), box_type, {:case, {:var, 0}, field_type, [{:MkBox, 1, {:var, 0}}]}}

    env =
      Env.empty()
      |> Inductive.declare(family, [ctor])
      |> Env.add_def(:mk, mk_type, mk_body, [Grade.unrestricted()])
      |> Env.add_def(:access, access_type, access_body, [Grade.unrestricted()])

    assert Grade.present?(:linear),
           "the premise of this test: a linear field is present, not erased"

    result =
      Emit.compile_and_load(env,
        module: Cure.Elab.EmitGradePredicateFixture,
        functions: [:mk, :access]
      )

    assert {:ok, mod} = result, "expected the module to compile and load, got: #{inspect(result)}"

    # Present at construction *and* bound by the pattern that reads it back:
    # an emitter that dropped the field from the `case` clause would not
    # recover the 42 it stored.
    assert mod.access(mod.mk(42)) == 42
  end
end
