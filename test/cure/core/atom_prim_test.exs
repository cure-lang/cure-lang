defmodule Cure.Core.AtomPrimTest do
  @moduledoc """
  `Atom` as an Int-tier PRIMITIVE base type WITH a literal node — the Core type
  node `{:atom_type}` (mirroring `{:int_type}`/`{:binary_type}`) evaluating to
  `{:vatom_type}` and inferring to `Type 0`, PLUS the literal node
  `{:atom_lit, a}` (mirroring `{:int_lit, n}`) evaluating to `{:vatom, a}` and
  inferring to `Atom`.

  Unlike `Binary` (values only via `@extern`), an `Atom` has first-class
  literals — a BEAM atom is its own canonical value, `==` is native, and Show is
  `atom_to_binary`. Literal conversion is atom identity: `:ok` converts with
  `:ok` but not with `:no`. This is the aligned analog of Idris's `PrimType` +
  `Constant`.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.{Context, Conv, Env, Kernel, Quote, Term, Serialize, Eval}
  alias Cure.Elab.Program

  defp ctx, do: Context.empty(Env.empty())

  test "kernel types the Atom base type at Type 0 and a literal at Atom" do
    assert {:ok, {:vtype, 0}} = Kernel.infer(ctx(), {:atom_type})
    assert {:ok, {:vatom_type}} = Kernel.infer(ctx(), {:atom_lit, :ok})
  end

  test "eval and reify round-trip the Atom type and a literal" do
    assert {:vatom_type} = Eval.eval({:atom_type}, [])
    assert {:vatom, :ok} = Eval.eval({:atom_lit, :ok}, [])
    assert Quote.reify({:vatom_type}) == {:atom_type}
    assert Quote.reify({:vatom, :ok}) == {:atom_lit, :ok}
  end

  test "definitional equality: same atom converts, distinct atoms do not" do
    assert Conv.conv?({:atom_type}, {:atom_type}, [], 0, Env.empty())
    refute Conv.conv?({:atom_type}, {:int_type}, [], 0, Env.empty())
    assert Conv.conv?({:atom_lit, :ok}, {:atom_lit, :ok}, [], 0, Env.empty())
    refute Conv.conv?({:atom_lit, :ok}, {:atom_lit, :no}, [], 0, Env.empty())
  end

  test "Atom nodes are well-formed Core terms that shift and substitute as atoms" do
    assert Term.term?({:atom_type})
    assert Term.term?({:atom_lit, :ok})
    refute Term.term?({:atom_lit, 7})
    assert Term.shift({:atom_type}, 3, 0) == {:atom_type}
    assert Term.shift({:atom_lit, :ok}, 3, 0) == {:atom_lit, :ok}
    assert Term.subst({:atom_type}, 0, {:int_lit, 7}) == {:atom_type}
    assert Term.subst({:atom_lit, :ok}, 0, {:int_lit, 7}) == {:atom_lit, :ok}
  end

  test "Atom nodes round-trip through the s-expression serializer" do
    {:ok, back} = Serialize.decode(Serialize.encode({:atom_type}))
    assert back == {:atom_type}
    {:ok, back2} = Serialize.decode(Serialize.encode({:atom_lit, :ok}))
    assert back2 == {:atom_lit, :ok}
    # A name that is not a bareword is emitted quoted; it must read back through
    # the `{:str, _}` symbol position too, not only the bareword `{:atom, _}` one.
    {:ok, back3} = Serialize.decode(Serialize.encode({:atom_lit, :"has space"}))
    assert back3 == {:atom_lit, :"has space"}
  end

  test "Atom nodes round-trip through external JSON form" do
    assert Term.from_external(Term.to_external({:atom_type})) == {:atom_type}
    assert Term.from_external(Term.to_external({:atom_lit, :ok})) == {:atom_lit, :ok}
  end

  test "an `Atom` signature elaborates to the primitive, not a free global :Atom" do
    {:ok, env} = Program.elaborate("mod M\n  fn f(a: Atom) -> Atom = a\nend\n")

    assert Env.get_def(env, :f).type ==
             {:pi, Cure.Core.Grade.unrestricted(), {:atom_type}, {:atom_type}}
  end
end
