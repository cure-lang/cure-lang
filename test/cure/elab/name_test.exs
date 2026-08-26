defmodule Cure.Elab.NameTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Name

  test "preserves content-derived identities containing hash characters" do
    name = :"Union<Int|Std.Bool#Bool>"

    assert Name.owner(name) == nil
    assert Name.base(name) == "Union<Int|Std.Bool#Bool>"
  end

  test "splits canonical owner-qualified names only at their owner separator" do
    name = :"Std.Functor#__impl_Functor_Std.List#List_fmap"

    assert Name.owner(name) == "Std.Functor"
    assert Name.base(name) == "__impl_Functor_Std.List#List_fmap"
  end

  describe "owner qualification" do
    # An owner is `[A-Za-z_][A-Za-z0-9_.]*`. These pin the accept/reject edges so
    # the scan that decides them cannot drift.
    test "accepts the owner alphabet" do
      assert Name.owner("Foo#bar") == "Foo"
      assert Name.owner("_Foo#bar") == "_Foo"
      assert Name.owner("F0.o_#bar") == "F0.o_"
      assert Name.owner("Std.Functor#fmap") == "Std.Functor"
    end

    test "rejects an empty, digit-led, or non-alphabet owner" do
      for name <- ["#bar", "1Foo#bar", "Foo Bar#bar", "Foo-Bar#bar", "Foo\nBar#bar", "\nFoo#bar"] do
        assert Name.owner(name) == nil, "expected #{inspect(name)} to have no owner"
        assert Name.base(name) == name, "expected #{inspect(name)} to keep its bare name"
      end
    end

    test "an unqualified name has no owner and is its own base" do
      assert Name.owner("bare") == nil
      assert Name.base("bare") == "bare"
      assert Name.qualified?("bare") == false
      assert Name.qualified?("Foo#bar") == true
    end

    # A newline is not in the owner alphabet, in ANY position. The original
    # implementation matched `~r/^[A-Za-z_][A-Za-z0-9_.]*$/`, whose `$` also
    # matches immediately before a trailing newline — so `"Foo\n"` was accepted
    # as an owner. That was an artifact of `$`, not an intended spelling:
    # owners are module names and nothing can construct one containing a
    # newline. The scan anchors at the true end of the string instead.
    test "rejects an owner with a trailing newline" do
      assert Name.owner("Foo\n#bar") == nil
      assert Name.base("Foo\n#bar") == "Foo\n#bar"
    end
  end

  describe "split/1" do
    # `owner/1` and `base/1` are defined through `split/1`, so these pin that the
    # single pass agrees with both halves rather than drifting from them.
    test "agrees with owner/1 and base/1" do
      for name <- [
            :"Std.Functor#fmap",
            :"Union<Int|Std.Bool#Bool>",
            :"Std.Functor#__impl_Functor_Std.List#List_fmap",
            :bare,
            :"1Foo#bar"
          ] do
        assert Name.split(name) == {Name.owner(name), Name.base(name)},
               "split/1 disagreed with owner/1 + base/1 for #{inspect(name)}"
      end
    end

    test "splits at the first separator only" do
      assert Name.split("Std.Functor#__impl_Functor_Std.List#List_fmap") ==
               {"Std.Functor", "__impl_Functor_Std.List#List_fmap"}
    end

    test "an unowned name is its own base" do
      assert Name.split("bare") == {nil, "bare"}
      assert Name.split("Union<Int|Std.Bool#Bool>") == {nil, "Union<Int|Std.Bool#Bool>"}
    end
  end

  describe "qualify/2" do
    test "round-trips through owner/1 and base/1" do
      name = Name.qualify("Std.List", "map")

      assert name == :"Std.List#map"
      assert Name.owner(name) == "Std.List"
      assert Name.base(name) == "map"
    end

    test "accepts atom and string spellings alike" do
      assert Name.qualify(:"Std.List", :map) == Name.qualify("Std.List", "map")
    end
  end
end
