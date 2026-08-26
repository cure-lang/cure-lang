defmodule Cure.Elab.AtomLiteralTest do
  @moduledoc """
  Surface elaboration + emit of atom literals (`:ok`) onto the Int-tier primitive
  `Atom` base type. A symbol literal `:ok` elaborates to Core `{:atom_lit, :ok}`
  of type `Atom`, and runs on the BEAM as the native atom `:ok`.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.{Program, Emit}

  test "an atom literal elaborates to {:atom_lit, _} : Atom" do
    {:ok, env} = Program.elaborate("mod M\n  fn tag() -> Atom = :ok\nend\n")
    d = Env.get_def(env, :tag)
    assert d.type == {:atom_type}
    assert d.body == {:atom_lit, :ok}
  end

  test "an atom literal runs end-to-end as the native BEAM atom" do
    {:ok, env} = Program.elaborate("mod M\n  fn tag() -> Atom = :millisecond\nend\n")
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.AtomLit", functions: [:tag])
    assert apply(m, :tag, []) == :millisecond
  end

  test "atom equality via struct_eq distinguishes distinct atoms" do
    src = """
    mod M
      fn same(a: Atom, b: Atom) -> Bool = a == b
    """

    {:ok, env} = Program.elaborate(src)
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.AtomEq", functions: [:same])
    assert apply(m, :same, [:ok, :ok]) == true
    assert apply(m, :same, [:ok, :no]) == false
  end
end
