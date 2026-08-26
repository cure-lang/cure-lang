defmodule Cure.Elab.ArgumentLabelsLoweringTest do
  @moduledoc """
  Ph2 Slice B/F: the parsed argument labels (Slice A) are lowered onto the
  function's def record as a telescope-aligned descriptor vector, readable via
  `Cure.Core.Env.labels/2`. Each parameter is `{:required, external_label}` (a
  two-name binder, label mandatory) or `{:optional, binder_name}` (a single-name
  binder, label optional — the binder name is retained so a written optional label
  can be validated). Labels erase before Core; codegen and resolution keys are
  unaffected regardless.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.Program

  defp elab!(src) do
    {:ok, env} = Program.elaborate(src)
    env
  end

  test "a mandatory (two-name) parameter lowers to a :required descriptor" do
    env = elab!("mod M\n  fn move(to dest: Int) -> Int = dest\nend\n")
    assert Env.labels(env, :"M#move") == [{:required, "to"}]
  end

  test "a mix of mandatory and optional parameters aligns descriptors by position" do
    env = elab!("mod M\n  fn blit(src: Int, to dest: Int) -> Int = dest\nend\n")
    assert Env.labels(env, :"M#blit") == [{:optional, "src"}, {:required, "to"}]
  end

  # A def with no MANDATORY labels still records its single-name binder names as
  # `{:optional, name}`, so a written optional label can be checked against them.
  test "a label-free def records optional descriptors carrying the binder names" do
    env = elab!("mod M\n  fn add(x: Int, y: Int) -> Int = x + y\nend\n")
    assert Env.labels(env, :"M#add") == [{:optional, "x"}, {:optional, "y"}]
  end
end
