defmodule Cure.Stdlib.MacroOnlyOtpArchitectureTest do
  use ExUnit.Case, async: true

  @surfaces %{
    "lib/std/actor.cure" => ["macro actor", "Std.Otp.start_link", "Std.ActorBehavior.actor_module"],
    "lib/std/fsm.cure" => ["macro fsm", "Std.Otp.start_statem", "Std.ActorBehavior.state_machine_module"],
    "lib/std/supervisor.cure" => ["macro sup", "Std.Otp.start_supervisor"],
    "lib/std/app.cure" => ["macro app", "Std.Otp.start_supervisor"]
  }

  test "OTP object surfaces are source macros over the ordinary typed OTP algebra" do
    Enum.each(@surfaces, fn {file, required} ->
      source = File.read!(file)

      Enum.each(required, fn fragment ->
        assert source =~ fragment, "#{file} lost macro architecture fragment #{fragment}"
      end)

      refute source =~ "@extern(Elixir.Cure.", "#{file} restored an Elixir Builtins bridge"
      refute source =~ ".Builtins", "#{file} restored a Builtins-backed convenience API"
    end)
  end

  test "actor and FSM share a transparent source-defined behavior substrate" do
    actor = File.read!("lib/std/actor.cure")
    fsm = File.read!("lib/std/fsm.cure")
    substrate = File.read!("lib/std/actor_behavior.cure")

    refute actor =~ "lift_module_isolated"
    refute fsm =~ "lift_module_isolated"

    assert substrate =~ "fn behavior_module"
    assert substrate =~ "lift_module_isolated(module_name, kind"
    assert substrate =~ "fn actor_module"
    assert substrate =~ "fn state_machine_module"

    refute substrate =~ "@extern(Elixir.Cure."
    refute substrate =~ ".Builtins"
    refute substrate =~ "Runtime"
  end

  test "OTP object surfaces expose only structured family rules" do
    source = @surfaces |> Map.keys() |> Enum.map_join("\n", &File.read!/1)

    for keyword <- ~w(actor fsm sup app) do
      refute Regex.match?(~r/syntax\s+#{keyword}\s+/, source),
             "restored legacy `syntax #{keyword} ...` rule"
    end

    refute source =~ "ActorContainers"
    refute source =~ "FsmContainers"
    refute source =~ "AppContainers"
    refute File.read!("lib/cure/compiler/parser.ex") =~ "legacy_block_ambiguity?"
  end

  test "no active standard-library OTP object module references the retired bridges" do
    forbidden = [
      "Cure.Actor.Builtins",
      "Cure.FSM.Builtins",
      "Cure.Sup.Builtins",
      "Cure.App.Builtins"
    ]

    source =
      @surfaces
      |> Map.keys()
      |> Enum.map_join("\n", &File.read!/1)

    Enum.each(forbidden, fn bridge ->
      refute source =~ bridge
    end)
  end
end
