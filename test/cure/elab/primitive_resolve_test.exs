defmodule Cure.Elab.PrimitiveResolveTest do
  @moduledoc """
  Bare `Int`/`Float`/`Binary` resolve to their Core nodes via the seeded floor,
  with no import (spec 2026-07-10-primitive-type-declarations). This is the
  behaviour the deleted `primitive_type/1` provided; it must survive on the
  env floor.
  """
  use ExUnit.Case, async: true
  alias Cure.Core.Env
  alias Cure.Elab.Program

  for {name, node} <- [{"Int", {:data, :"Std.Int#Int", [], []}}, {"Float", {:float_type}}, {"Binary", {:binary_type}}] do
    test "bare #{name} resolves to #{inspect(node)} with no import" do
      {:ok, env} =
        Program.elaborate("mod M\n  fn f(x: #{unquote(name)}) -> #{unquote(name)} = x\nend\n")

      assert Env.get_def(env, :f).type ==
               {:pi, Cure.Core.Grade.unrestricted(), unquote(Macro.escape(node)), unquote(Macro.escape(node))}
    end
  end

  test "a primitive as an enum-ADT constructor field resolves via the floor" do
    # Exercises the type_to_core path (enum field types), distinct from the
    # param/return resolve_index_name path above.
    {:ok, env} = Program.elaborate("mod M\n  type Boxed = Box(Int)\nend\n")
    box = Cure.Core.Inductive.get_ctor(env, :Box)
    assert [{_name, {:data, :"Std.Int#Int", [], []}}] = box.args
  end
end
