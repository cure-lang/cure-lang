defmodule Cure.Core.BinaryPrimTest do
  @moduledoc """
  #3 (batch 2026-07-10): `Binary` as an Int-tier PRIMITIVE base type — the Core
  node `{:binary_type}` mirroring `{:int_type}`/`{:float_type}`, evaluating to
  the value `{:vbinary_type}` and inferring to `Type 0`.

  Before this, a `Binary` signature resolved to the free neutral `{:global,
  :Binary}` — an UNDECLARED global that only typechecked by reflexive
  self-conversion (the faking-era pattern). Making it a real primitive gives it
  a proper kernel identity: it is a canonical type head, converts structurally,
  is a rigid index, and round-trips through serialize / external JSON.

  This is the BASE TYPE ONLY. A `Binary` literal node and byte_size / bit-syntax
  ops are a deliberate fast-follow (spec 2026-07-10-length-indexed-binary), so
  values of `Binary` still arrive solely via `@extern` (e.g. Std.Binary's
  `to_binary`), which is exactly the inert-carrier discipline.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Kernel, Quote, Term, Serialize, Eval}
  alias Cure.Elab.Program

  defp ctx, do: Context.empty(Env.empty())

  test "kernel types the Binary base type at Type 0" do
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx(), {:binary_type})
  end

  test "eval and reify round-trip the Binary type" do
    assert {:vbinary_type} = Eval.eval({:binary_type}, [])
    assert Quote.reify({:vbinary_type}) == {:binary_type}
  end

  test "two Binary types are definitionally equal" do
    assert Conv.conv?({:binary_type}, {:binary_type}, [], 0, Env.empty())
    refute Conv.conv?({:binary_type}, {:int_type}, [], 0, Env.empty())
  end

  test "Binary is a well-formed Core term that shifts and substitutes as an atom" do
    assert Term.term?({:binary_type})
    assert Term.shift({:binary_type}, 3, 0) == {:binary_type}
    assert Term.subst({:binary_type}, 0, {:int_lit, 7}) == {:binary_type}
  end

  test "Binary round-trips through the s-expression serializer" do
    {:ok, back} = Serialize.decode(Serialize.encode({:binary_type}))
    assert back == {:binary_type}
  end

  test "Binary round-trips through external JSON form" do
    assert Term.from_external(Term.to_external({:binary_type})) == {:binary_type}
  end

  test "a `Binary` signature elaborates to the primitive, not the free global :Binary" do
    {:ok, env} = Program.elaborate("mod M\n  fn f(b: Binary) -> Binary = b\nend\n")

    assert Env.get_def(env, :f).type ==
             {:pi, Cure.Core.Grade.unrestricted(), {:binary_type}, {:binary_type}}
  end
end
