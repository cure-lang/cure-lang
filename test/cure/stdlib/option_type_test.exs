defmodule Cure.Stdlib.OptionTypeTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program
  alias Cure.Core.Inductive

  # `Option(t)` must be a REAL inductive type a user can read in the stdlib, not
  # an undeclared tag the classic pipeline tolerated. `Std.Option` declares it,
  # so `Some`/`None` resolve as real constructors of a registered `Option`
  # family. (Full dependent elaboration of `option.cure` additionally needs the
  # tuple wave — its `zip` builds a `%[va, vb]` tuple checked against the opaque
  # `Tuple` type — which is out of scope here; this test covers the declaration.)

  test "Option(t) = Some(t) | None() is a real, usable inductive" do
    src = """
    mod UseOption
      type Option(t) = Some(t) | None()
      fn get(o: Option(Int)) -> Int =
        match o
          Some(v) -> v
          None() -> 0
    end
    """

    assert {:ok, env} = Program.elaborate(src)
    assert Inductive.get_family(env, :Option)
    assert Inductive.get_ctor(env, :Some)
    assert Inductive.get_ctor(env, :None)
  end

  test "Std.Option declares the Option type in-source (inspectable)" do
    src = File.read!("lib/std/option.cure")
    assert src =~ "type Option(t) = Some(t) | None()"
  end
end
