defmodule Cure.Stdlib.OtpMelquiadesTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "ASCII and envelope operators delegate to typed tell" do
    for operator <- ["<-|", "✉"] do
      assert {:ok, _env} =
               Program.elaborate("""
               mod M
                 use Std.Otp

                 type Command = Increment | Reset

                 fn send_it(pid: Pid(Command)) -> Effect(Unit) =
                   pid #{operator} Increment()
               """)
    end
  end

  test "both operators enforce the destination's message index" do
    for operator <- ["<-|", "✉"] do
      assert {:error, _reason} =
               Program.elaborate("""
               mod M
                 use Std.Otp

                 type Command = Increment | Reset

                 fn bad(pid: Pid(Command)) -> Effect(Unit) =
                   pid #{operator} 42
               """)
    end
  end

  test "Melquiades syntax is not in scope without its Std.Otp provider" do
    assert {:error, errors} =
             Program.elaborate("""
             mod M
               fn bad(left: Int, right: Int) -> Int = left <-| right
             """)

    assert Enum.any?(errors, &match?({:unexpected_token, %{token_type: :melquiades}}, &1))
  end
end
