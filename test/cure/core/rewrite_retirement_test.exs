defmodule Cure.Core.RewriteRetirementTest do
  @moduledoc """
  Phase C, removal group A: the primitive `{:rewrite, proof, motive, body}`
  Core form is RETIRED (no producers since Phase B — the elaborator emits the
  J/subst `:case` transport). The kernel/term/serializer clauses for it are
  stripped and the form becomes unknown grammar.

  RED before the group-A removal commit (the form still round-trips); GREEN
  after. The `{:eq}`/`{:refl}` twins live in `eq_refl_retirement_test.exs`
  (removal group B).
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Kernel, Serialize, Term}
  alias Cure.Elab.Program
  import Cure.TestSupport.RetiredNode, only: [opaque: 1]

  @nat {:data, :Nat, [], []}
  defp z, do: {:ctor, :Z, []}

  defp base_sig do
    {:ok, sig} = Program.elaborate("mod M\nend\n")
    sig
  end

  test "Kernel.infer no longer accepts a primitive {:rewrite} node" do
    sig = base_sig()

    eq_val =
      Eval.eval({:data, :Equivalent, [@nat], [z(), z()]}, Context.env(Context.empty(sig)))

    ctx = Context.extend(Context.empty(sig), eq_val)
    node = {:rewrite, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, z()}

    assert_raise FunctionClauseError, fn -> Kernel.infer(ctx, opaque(node)) end
  end

  test "Term.term?/1 rejects {:rewrite}" do
    refute Term.term?({:rewrite, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, z()})
  end

  test "Term.to_external/1 refuses {:rewrite}" do
    assert_raise FunctionClauseError, fn ->
      Term.to_external(opaque({:rewrite, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), @nat, @nat}, z()}))
    end
  end

  test "serializer neither encodes nor decodes {:rewrite}" do
    assert_raise FunctionClauseError, fn ->
      Serialize.encode(
        opaque({:rewrite, {:var, 0}, {:lam, Cure.Core.Grade.unrestricted(), {:int_type}, {:int_type}}, {:int_lit, 1}})
      )
    end

    assert {:error, _} =
             Serialize.decode("(rewrite (var 0) (lam (int-type) (int-type)) (int 1))")
  end
end
