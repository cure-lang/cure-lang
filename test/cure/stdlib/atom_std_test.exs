defmodule Cure.Stdlib.AtomStdTest do
  @moduledoc """
  `Std.Atom` gives the primitive `Atom` base type a visible, inspectable home in
  the stdlib — the user-facing half of the Int-tier primitive (mirroring
  `Std.Int`/`Std.Float`/`Std.Binary`). `@builtin(:atom) primitive Atom` confirms
  against the kernel floor `put_primitive("Atom", {:atom_type})`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  test "Std.Atom elaborates and declares the Atom primitive" do
    assert {:ok, env} = Program.elaborate(File.read!("lib/std/atom.cure"))
    assert Cure.Core.Env.primitive(env, "Atom") == {:atom_type}
  end

  test "a program that uses Std.Atom resolves Atom to the primitive" do
    src = "mod M\n  use Std.Atom\n  fn tag(a: Atom) -> Atom = a\nend\n"
    {:ok, env} = Program.elaborate(src)

    assert Cure.Core.Env.get_def(env, :tag).type ==
             {:pi, Cure.Core.Grade.unrestricted(), {:atom_type}, {:atom_type}}
  end
end
