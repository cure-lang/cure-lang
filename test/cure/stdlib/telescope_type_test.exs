defmodule Cure.Stdlib.TelescopeTypeTest do
  @moduledoc """
  `Std.Telescope` declares the telescope as a real, visible inductive type —
  the reified *shape* of a tuple (which types, in order), terminated by the
  empty telescope. This is the Agda/Idris telescope-as-data: `Empty` and a
  `More(head, rest)` cons of a `Type` onto a shorter telescope.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Inductive

  defp elab(src) do
    try do
      Cure.Elab.Program.elaborate(src)
    rescue
      e -> {:raise, Exception.message(e)}
    catch
      k, v -> {:raise, "#{inspect(k)}: #{inspect(v)}"}
    end
  end

  test "Std.Telescope declares Telescope as an inductive with Empty and More constructors" do
    src = File.read!("lib/std/telescope.cure")
    assert {:ok, env} = elab(src)
    ctor_names = env |> Inductive.ctors_of(:Telescope) |> Enum.map(& &1.name) |> Enum.sort()
    assert ctor_names == [:"Std.Telescope#Empty", :"Std.Telescope#More"]
  end
end
