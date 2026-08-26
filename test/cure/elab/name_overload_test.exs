defmodule Cure.Elab.NameOverloadTest do
  use ExUnit.Case, async: true
  alias Cure.Elab.Name

  test "overload_key appends ~ordinal to a bare base" do
    assert Name.overload_key(:plus, 0) == :"plus~0"
    assert Name.overload_key(:plus, 1) == :"plus~1"
  end

  test "overload_key appends ~ordinal to the base of a qualified key" do
    assert Name.overload_key(:"Mod#plus", 0) == :"Mod#plus~0"
  end

  test "overload_member? detects the discriminator, ignores plain keys" do
    assert Name.overload_member?(:"Mod#plus~0")
    assert Name.overload_member?(:"plus~2")
    refute Name.overload_member?(:"Mod#plus")
    refute Name.overload_member?(:plus)
  end

  test "overload_base strips the discriminator to the plain base name" do
    assert Name.overload_base(:"Mod#plus~0") == "plus"
    assert Name.overload_base(:"plus~1") == "plus"
    assert Name.overload_base(:"Mod#plus") == "plus"
    assert Name.overload_base(:plus) == "plus"
  end

  test "base/1 still returns the full discriminated base (emit distinctness)" do
    assert Name.base(:"Mod#plus~0") == "plus~0"
    assert Name.owner(:"Mod#plus~0") == "Mod"
  end
end
