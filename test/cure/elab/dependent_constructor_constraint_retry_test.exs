defmodule Cure.Elab.DependentConstructorConstraintRetryTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.{CallAttemptProfile, Program}

  @source """
  mod DependentConstructorConstraintRetry
  type Witness indices (n: Nat)
    Witnessed : Witness(n)

  type At indices (n: Nat)
    ZeroAt : At(Z())
    SuccAt : At(n) -> At(S(n))

  type Packed indices (n: Nat)
    Pack : {m: Nat} -> (witness: Witness(m)) -> (at: At(m)) -> Packed(m)

  fn consume({n: Nat}, packed: Packed(n)) -> Nat = 0
  fn pack() -> Nat = consume(Pack(Witnessed(), ZeroAt()))
  end
  """

  test "nested dependent fields do not get retried after a stable context" do
    {{{:ok, _env}, metrics}, attempts} =
      CallAttemptProfile.run(fn ->
        result = Program.elaborate(@source, file: "dependent_constructor_retry.cure")
        {result, CallAttemptProfile.metrics()}
      end)

    assert metrics[:constructor_field_attempts] >= 1

    assert Enum.find(attempts, fn attempt ->
             attempt.callee == "Witnessed" and attempt.strategy == :constructor_bidirectional
           end).count == 1
  end

  test "a rigid nested field remains a structured constructor error" do
    source = """
    mod DependentConstructorRigidMismatch
      type List(a: Type) = Nil | Cons(a, List(a))
      type Weird indices (a: Type)
        Bad : {b: Type} -> List(b) -> Weird(String)
      fn bad() -> Weird(Int) = Bad(Nil())
    end
    """

    assert {:error, error} = Program.elaborate(source, file: "dependent_constructor_rigid.cure")

    assert {:unsolved_metavariables, :"DependentConstructorRigidMismatch#Nil"} =
             Program.semantic_error(error)
  end
end
