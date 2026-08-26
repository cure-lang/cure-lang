defmodule Cure.Core.EqReflRetirementTest do
  @moduledoc """
  Phase C, removal group B: the primitive `{:eq, ty, a, b}` / `{:refl, a}` Core
  forms (and their value forms `{:veq}`/`{:vrefl}`) are RETIRED — every
  producer builds the inductive `{:data, :Equivalent, …}` / `{:ctor,
  :reflexive, …}`. The kernel/eval/quote/term/serializer clauses for them are
  stripped and the forms become unknown grammar.

  RED before the group-B removal commit (the forms still round-trip); GREEN
  after. The `{:rewrite}` twin lives in `rewrite_retirement_test.exs` (group A).
  The positive control pins that the inductive replacements keep working, so
  this file alone distinguishes "retired primitive" from "broken equality".
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Eval, Kernel, Serialize, Term}
  alias Cure.Elab.Program
  import Cure.TestSupport.RetiredNode, only: [opaque: 1]

  @nat {:data, :"Std.Nat#Nat", [], []}
  defp z, do: {:ctor, :Z, []}
  defp s(n), do: {:ctor, :S, [n]}

  defp base_sig do
    {:ok, sig} = Program.elaborate("mod M\nend\n")
    sig
  end

  defp eq_ty(sig, ty, a, b),
    do:
      Eval.eval(
        {:data, :"Std.Equivalent#Equivalent", [ty], [a, b]},
        Context.env(Context.empty(sig))
      )

  test "Kernel.infer no longer accepts primitive {:eq} / {:refl} nodes" do
    sig = base_sig()
    ctx = Context.empty(sig)

    assert_raise FunctionClauseError, fn ->
      Kernel.infer(ctx, opaque({:eq, @nat, z(), z()}))
    end

    assert_raise FunctionClauseError, fn ->
      Kernel.infer(ctx, opaque({:refl, z()}))
    end
  end

  test "Term.term?/1 rejects {:eq} and {:refl}" do
    refute Term.term?({:eq, @nat, z(), z()})
    refute Term.term?({:refl, z()})
  end

  test "Term.to_external/1 refuses {:eq} and {:refl}" do
    assert_raise FunctionClauseError, fn -> Term.to_external(opaque({:refl, z()})) end

    assert_raise FunctionClauseError, fn ->
      Term.to_external(opaque({:eq, @nat, z(), z()}))
    end
  end

  test "serializer neither encodes nor decodes {:eq} / {:refl}" do
    assert_raise FunctionClauseError, fn -> Serialize.encode(opaque({:refl, {:int_lit, 1}})) end

    assert_raise FunctionClauseError, fn ->
      Serialize.encode(opaque({:eq, {:int_type}, {:int_lit, 1}, {:int_lit, 1}}))
    end

    assert {:error, _} = Serialize.decode("(eq (int-type) (int 1) (int 1))")
    assert {:error, _} = Serialize.decode("(refl (int 1))")
  end

  test "positive control: the inductive Equivalent/reflexive forms still work" do
    sig = base_sig()
    ctx = Context.empty(sig)

    # reflexive checks against Equivalent at convertible endpoints…
    assert :ok = Kernel.check(ctx, {:ctor, :reflexive, [z()]}, eq_ty(sig, @nat, z(), z()))
    # …and still refuses distinct endpoints.
    assert {:error, _} =
             Kernel.check(ctx, {:ctor, :reflexive, [z()]}, eq_ty(sig, @nat, z(), s(z())))

    # The inductive type/ctor round-trip the serializer.
    eq_term = {:data, :Equivalent, [@nat], [z(), z()]}
    assert {:ok, ^eq_term} = Serialize.decode(Serialize.encode(eq_term))
    refl_term = {:ctor, :reflexive, [z()]}
    assert {:ok, ^refl_term} = Serialize.decode(Serialize.encode(refl_term))
  end
end
