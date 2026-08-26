defmodule Cure.Stdlib.BinaryTest do
  use ExUnit.Case, async: false

  # `Cure.Std.Binary` is loaded dynamically by `Cure.Stdlib.Preload` in
  # `setup_all`; Elixir's compile-time checker doesn't see it.
  @compile {:no_warn_undefined, :"Cure.Std.Binary"}

  @bin :"Cure.Std.Binary"

  setup_all do
    Cure.Stdlib.Preload.preload(examples: false, kind: :all)
    :ok
  end

  # The bridge between the two string representations (#28): a `List(Char)` (a
  # cons spine of code-point ints — how string literals now elaborate) and a
  # `Binary` (the BEAM binary the OTP `:string`/`:binary` externs need). `Char`
  # erases to its code-point int, so a `List(Char)` erases to a plain int list.
  test "to_binary turns a List(Char) into the UTF-8 Binary" do
    assert @bin.to_binary([?h, ?i]) == "hi"
  end

  test "from_binary turns a Binary into a List(Char) of code points" do
    assert @bin.from_binary("hi") == [?h, ?i]
  end

  test "round-trips a multi-byte code point (é = 233)" do
    cs = [?c, ?a, ?f, ?e, 233]
    assert @bin.from_binary(@bin.to_binary(cs)) == cs
  end
end
