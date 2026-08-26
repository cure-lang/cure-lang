defmodule Cure.Elab.SignatureForwardReferenceIdentityTest do
  use ExUnit.Case, async: true

  alias Cure.Audit.Refs
  alias Cure.Core.Env
  alias Cure.Elab.Program

  test "a later local function has one canonical identity inside earlier signatures" do
    source = """
    mod SignatureForwardReference
      fn earlier(x: Nat, proof: Equivalent(Nat, later(x), x)) -> Equivalent(Nat, later(x), x) = proof
      fn later(x: Nat) -> Nat = x
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert %{type: type} = Env.get_def(env, :earlier)

    globals = Refs.globals(type)
    assert :"SignatureForwardReference#later" in globals
    refute :later in globals
  end
end
