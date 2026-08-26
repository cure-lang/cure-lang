defmodule Cure.Elab.LetLinearSoundnessTest do
  @moduledoc """
  Soundness of the `{0,1,ω}` usage check through a `let` binding.

  A `let x = v in b` uses `v`'s resources once per use of `x` (the QTT / Idris
  `LinearCheck` accounting: `let` is transparent for usage — `b[x := v]`). The
  original `Relevance` `:let` clause seq'd `v`'s usage ONCE regardless of how many
  times `x` was used, so a linear resource ALIASED by a `let` and then used twice
  was laundered to a single use — accepted where Idris rejects. That is a
  *soundness* hole (it lets a linear reply capability be duplicated), verified
  against the Idris oracle:

    * `let x = c in (x, x)`         c linear -> Idris REJECT, Cure had ACCEPT (bug)
    * `let x = consume(c) in (x,x)` c linear -> Idris REJECT, Cure had ACCEPT (bug)
    * `let x = c in x`              c linear -> Idris ACCEPT (used once)
    * `let x = consume(c) in x`     c linear -> Idris ACCEPT (used once)

  The fix scales `v`'s usage by `x`'s usage before sequencing it with the body.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  defp verdict(src) do
    case Program.elaborate(src) do
      {:ok, _} -> :accept
      {:error, _} -> :reject
    end
  end

  @preamble """
    type Box = MkBox
    type Widget = MkWidget
    type Pair = MkPair(Box, Box)
    type WPair = MkWPair(Widget, Widget)
    fn consume(@linear c : Box) -> Widget = match c
      MkBox() -> MkWidget
  """

  defp mod(name, defs), do: "mod #{name}\n#{@preamble}#{defs}\nend\n"

  describe "a linear let-value used more than once is rejected (was laundered)" do
    test "alias then duplicate: let x = c in MkPair(x, x)" do
      src = mod("AliasDup", "  fn f(@linear c : Box) -> Pair = let x = c in MkPair(x, x)")
      assert verdict(src) == :reject
    end

    test "consume then duplicate: let x = consume(c) in MkWPair(x, x)" do
      src = mod("ConsumeDup", "  fn f(@linear c : Box) -> WPair = let x = consume(c) in MkWPair(x, x)")
      assert verdict(src) == :reject
    end
  end

  describe "a linear let-value used exactly once is still accepted" do
    test "alias then use once: let x = c in <consume x>" do
      src = mod("AliasOnce", "  fn f(@linear c : Box) -> Widget = let x = c in consume(x)")
      assert verdict(src) == :accept
    end

    test "consume then use once: let x = consume(c) in x" do
      src = mod("ConsumeOnce", "  fn f(@linear c : Box) -> Widget = let x = consume(c) in x")
      assert verdict(src) == :accept
    end
  end

  describe "the hole let a linear reply capability be duplicated (obligation 1)" do
    @otp """
      type Reply0 = R0
      type Req = GetCount | Ping
      fn ReplyOf(r: Req) -> Type = match r
        GetCount() -> Reply0
        Ping()     -> Reply0
      type ReplyCap(r: Req) indices ()
        MkCap : ReplyCap(r)
      type Replied = Done
      type DPair = MkDPair(Replied, Replied)
      fn reply({r: Req}, @linear cap : ReplyCap(r), v: ReplyOf(r)) -> Replied =
        match cap
          MkCap() -> Done
      fn handle(r: Req) -> ReplyOf(r) = match r
        GetCount() -> R0
        Ping()     -> R0
    """

    test "duplicating cap through a let is rejected" do
      src = """
      mod LaunderCap
      #{@otp}
        fn serve(r: Req, @linear cap : ReplyCap(r)) -> DPair =
          let x = cap in MkDPair(reply(x, handle(r)), reply(x, handle(r)))
      end
      """

      assert verdict(src) == :reject
    end

    test "using cap exactly once through a let is still accepted" do
      src = """
      mod OneShotCap
      #{@otp}
        fn serve(r: Req, @linear cap : ReplyCap(r)) -> Replied =
          let x = cap in reply(x, handle(r))
      end
      """

      assert verdict(src) == :accept
    end
  end
end
