defmodule Cure.Elab.AutoDeriveEquatableTest do
  @moduledoc """
  Sole-route `==` auto-derives a structural `Equatable` for any ADT that lacks a
  hand-written instance, via `Std.Builtin.struct_eq`. These tests lock the three
  properties that make the derivation safe:

    1. the derived instance computes exactly what the old builtin `struct_eq`
       fallback did (constructor tag + fields, structurally);
    2. a hand-written instance is authoritative — auto-derivation never overwrites
       it (a regression guard: the derived method's mangled name, and hence its
       coherence `ref`, is byte-identical to the hand-written one, so the skip must
       key on head presence, not ref equality); and
    3. two instances for one `(interface, head)` remain an overlap error — the
       derivation does not weaken global coherence.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.{Emit, Program}

  # Load a self-contained module by emitting every one of its own definitions,
  # including compiler-synthesised ones (the auto-derived `__impl_Equatable_…`
  # method), which a hand-picked `functions:` list would omit. Local defs are
  # keyed `"<Mod>#<name>"` in the elaborated env; strip the owner prefix back to the
  # bare emit name.
  defp load(src, module, prefix) do
    {:ok, env} = Program.elaborate(src)

    names =
      for k <- Map.keys(env.defs),
          s = Atom.to_string(k),
          String.starts_with?(s, prefix),
          do: String.to_atom(String.replace_prefix(s, prefix, ""))

    {:ok, mod} = Emit.compile_and_load(env, module: module, functions: names)
    mod
  end

  test "auto-derived structural Equatable matches struct_eq: tag and fields" do
    src = """
    mod AD
      type Shape = Circle(Int) | Square(Int)
      fn eq(a: Shape, b: Shape) -> Bool = a == b
      fn mk_c(n: Int) -> Shape = Circle(n)
      fn mk_s(n: Int) -> Shape = Square(n)
    end
    """

    m = load(src, :"Cure.AD", "AD#")
    c3 = apply(m, :mk_c, [3])
    c4 = apply(m, :mk_c, [4])
    s3 = apply(m, :mk_s, [3])

    assert apply(m, :eq, [c3, c3]) == true
    # same constructor, different field
    assert apply(m, :eq, [c3, c4]) == false
    # different constructor, same field payload
    assert apply(m, :eq, [c3, s3]) == false
  end

  test "a hand-written instance wins — auto-derivation does not overwrite it" do
    # The override reports every pair equal; the auto-derived structural instance
    # would report `On == Off` as false. Observing `true` proves the hand-written
    # instance, not the derived one, is the live dictionary.
    src = """
    mod OV
      type Flag = On | Off
      implementation Equatable for Flag
        fn `==`(a: Flag, b: Flag) -> Bool = true
      fn eq(a: Flag, b: Flag) -> Bool = a == b
      fn mk_on() -> Flag = On
      fn mk_off() -> Flag = Off
    end
    """

    m = load(src, :"Cure.OV", "OV#")

    assert apply(m, :eq, [apply(m, :mk_on, []), apply(m, :mk_off, [])]) == true
  end

  test "a second Equatable instance for the same head is an overlap error" do
    src = """
    mod DUP
      implementation Equatable for Int
        fn `==`(a: Int, b: Int) -> Bool = true
    end
    """

    assert {:error, {:overlapping_instance, %{interface: :Equatable, head: :"Std.Int#Int"}}} =
             Program.elaborate(src)
  end
end
