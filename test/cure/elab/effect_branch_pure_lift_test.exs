defmodule Cure.Elab.EffectBranchPureLiftTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # A branch body that is a PURE value under an `Effect(R)` goal is lifted with
  # `pure`, exactly as the trailing expression of an effectful `let`-block is
  # (design 2026-07-09-effect-type-former §5.1). That lift reached `if` arms and
  # ordinary bodies but not `match` arms whose body is an introduction form: a
  # tuple or a list arm was checked directly against the `Effect(...)` goal (no
  # effect head to check a Σ against), and a data constructor has no inference
  # rule at all, so neither could ever be lifted.
  #
  # This is the shape EVERY gen_server callback has:
  #   handle_cast(...) -> Effect(Tuple(Atom, State)) = match message
  #     Inc -> %[:noreply, state + 1]

  test "a tuple match-arm is lifted into an Effect goal" do
    src = """
    mod M
      type Cmd = Inc | Dec

      fn step(m: Cmd, s: Int) -> Effect(Tuple(Atom, Int)) = match m
        Inc -> %[:noreply, s + 1]
        Dec -> %[:noreply, s - 1]
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a list match-arm is lifted into an Effect goal" do
    src = """
    mod M
      use Std.List

      type Cmd = Keep | Drop

      fn pick(m: Cmd, xs: List(Int)) -> Effect(List(Int)) = match m
        Keep -> xs
        Drop -> []
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "an effectful match-arm still elaborates as an effect, not a lifted pure value" do
    src = """
    mod M
      @extern(:erlang, :yield, 0)
      fn sched_yield() -> Effect(Unit)

      type Cmd = Go | Stay

      fn run(m: Cmd) -> Effect(Unit) = match m
        Go -> sched_yield()
        Stay -> sched_yield()
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a mistyped tuple match-arm is still rejected under an Effect goal" do
    src = """
    mod M
      type Cmd = Inc | Dec

      fn step(m: Cmd, s: Int) -> Effect(Tuple(Atom, Int)) = match m
        Inc -> %[:noreply, :not_an_int]
        Dec -> %[:noreply, s]
    """

    assert {:error, _reason} = Program.elaborate(src)
  end
end
