defmodule Cure.Elab.CallAttemptProfileTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.CallAttemptProfile

  test "aggregates candidate attempts by the complete diagnostic identity" do
    call = %{
      declaration: :"Bench#answer",
      span: {4, 3, 4, 9},
      callee: "choose",
      expected_type: :inference
    }

    {result, attempts} =
      CallAttemptProfile.run(fn ->
        CallAttemptProfile.with_call(call, fn ->
          assert {:error, {:conversion_failure, :left}} =
                   CallAttemptProfile.attempt(:"A#choose", :bidirectional, fn ->
                     {:error, {:conversion_failure, :left}}
                   end)

          assert {:error, {:conversion_failure, :right}} =
                   CallAttemptProfile.attempt(:"A#choose", :bidirectional, fn ->
                     {:error, {:conversion_failure, :right}}
                   end)

          CallAttemptProfile.attempt(:"B#choose", :bidirectional, fn -> {:ok, :term, :type} end)
        end)
      end)

    assert result == {:ok, :term, :type}

    assert attempts == [
             %{
               declaration: :"Bench#answer",
               span: {4, 3, 4, 9},
               callee: "choose",
               expected_type: :inference,
               candidate: :"A#choose",
               strategy: :bidirectional,
               outcome: {:error, :conversion_failure},
               count: 2
             },
             %{
               declaration: :"Bench#answer",
               span: {4, 3, 4, 9},
               callee: "choose",
               expected_type: :inference,
               candidate: :"B#choose",
               strategy: :bidirectional,
               outcome: :success,
               count: 1
             }
           ]
  end

  test "is a no-op outside its profiling scope" do
    before = Process.get()

    assert CallAttemptProfile.attempt(:candidate, :direct, fn -> {:ok, :term, :type} end) ==
             {:ok, :term, :type}

    assert Process.get() == before
  end

  test "the elaborator reports authored call and canonical candidate identities" do
    source = """
    mod AttemptProfileProbe
      fn id(x: Int) -> Int = x
      fn answer() -> Int = id(42)
    """

    {result, attempts} = CallAttemptProfile.run(fn -> Cure.Elab.Program.elaborate(source) end)

    assert {:ok, _env} = result

    assert Enum.any?(attempts, fn attempt ->
             attempt.declaration == :"AttemptProfileProbe#answer" and
               attempt.callee == "id" and
               attempt.candidate == :"AttemptProfileProbe#id" and
               attempt.count >= 1 and
               attempt.outcome == :success and
               not is_nil(attempt.span)
           end)
  end

  test "a list literal constructs its Core spine without candidate dispatch" do
    source = """
    mod CheckedCallProfileProbe
      use Std.Syntax
      fn build() -> Syntax = block([Node(:block, [], [])])
    """

    {result, attempts} = CallAttemptProfile.run(fn -> Cure.Elab.Program.elaborate(source) end)

    assert {:ok, _env} = result

    call_attempts =
      Enum.filter(attempts, fn attempt ->
        attempt.declaration == :"CheckedCallProfileProbe#build" and attempt.callee == "block"
      end)

    assert Enum.any?(call_attempts, &(&1.strategy == :scoped_infer and &1.outcome == :success))

    refute Enum.any?(attempts, fn attempt ->
             attempt.declaration == :"CheckedCallProfileProbe#build" and attempt.callee in ["Cons", "Nil"]
           end)
  end

  test "decoded literal descriptor spelling does not re-enter the character literal protocol" do
    source = """
    mod DescriptorCharacterProfileProbe
      use Std.String
      fn value() -> String = "hello"
    """

    {result, attempts} = CallAttemptProfile.run(fn -> Cure.Elab.Program.elaborate(source) end)

    assert {:ok, _env} = result

    assert Enum.any?(attempts, fn attempt ->
             attempt.declaration == :"DescriptorCharacterProfileProbe#value" and
               attempt.callee == "StringLiteral" and attempt.outcome == :success
           end)

    refute Enum.any?(attempts, fn attempt ->
             attempt.declaration == :"DescriptorCharacterProfileProbe#value" and
               attempt.callee == "CharacterLiteral"
           end)
  end
end
