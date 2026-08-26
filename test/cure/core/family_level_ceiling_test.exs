defmodule Cure.Core.FamilyLevelCeilingTest do
  @moduledoc """
  A family declaration must respect the fixed predicative ceiling
  (`Type0 : Type1 : Type2`). `check_family` validated the param/index telescopes
  but never range-checked the declared `level`, so a family could be admitted at
  an arbitrary `Type k` above the ceiling — inconsistent with the hierarchy the
  rest of the kernel enforces.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.{Env, Inductive, Kernel, Universe}

  defp check(level) do
    fam = Inductive.family(:Foo, [], [], level)
    Kernel.check_family(Env.empty(), fam)
  end

  test "a family at the ceiling is accepted" do
    assert :ok == check(Universe.ceiling())
  end

  test "a family above the ceiling is rejected" do
    assert {:error, :universe_ceiling} == check(Universe.ceiling() + 1)
  end
end
