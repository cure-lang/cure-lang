defmodule Cure.Elab.DependentConstructorConstraintRetryTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.{AttemptCache, CallAttemptProfile, Program}

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
    assert metrics[:constructor_field_attempts] <= 4
    assert metrics[:constructor_field_retries] >= 1
    assert metrics[:constructor_field_wakeups] >= 1

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

  test "a rigid field mismatch is not converted into an unsolved-field retry" do
    source = """
    mod DependentConstructorRigidField
      type Bit = F | T
      type Pair(a: Type, b: Type) = MkPair(a, b)
      type Wrapped indices (a: Type)
        Bad : {b: Type} -> Pair(b, Nat) -> Wrapped(a)
      fn bad() -> Wrapped(Int) = Bad(MkPair(Z(), T()))
    end
    """

    assert {:error, error} = Program.elaborate(source, file: "dependent_constructor_rigid_field.cure")

    assert {:index_mismatch,
            {:cannot_unify, {:data, :"Std.Nat#Nat", [], []}, {:data, :"DependentConstructorRigidField#Bit", [], []}}} =
             Program.semantic_error(error)
  end

  test "attempt-local normalization cache is scoped and reports hits" do
    refute AttemptCache.active?()

    AttemptCache.scope(fn ->
      assert AttemptCache.active?()

      key = {:probe, :normalized_term}

      assert {:miss, {:normalized, :term}} =
               AttemptCache.fetch(:normalize, key, fn -> {:normalized, :term} end)

      assert {:hit, {:normalized, :term}} =
               AttemptCache.fetch(:normalize, key, fn -> flunk("cache miss on repeated term") end)
    end)

    refute AttemptCache.active?()
  end
end
