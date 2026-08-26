defmodule Cure.Stdlib.DecisionTest do
  use ExUnit.Case, async: false

  # `Cure.Std.Decision` is loaded dynamically by `Cure.Stdlib.Preload` in
  # `setup_all`; Elixir's compile-time checker doesn't see it.
  @compile {:no_warn_undefined, :"Cure.Std.Decision"}

  @dec :"Cure.Std.Decision"

  setup_all do
    Cure.Stdlib.Preload.preload(examples: false, kind: :all)
    :ok
  end

  test "equivalent? of equal Bools is a Yes carrying a proof" do
    assert @dec.is_yes(@dec.equivalent?(true, true)) == true
    assert @dec.is_no(@dec.equivalent?(true, true)) == false

    assert @dec.is_yes(@dec.equivalent?(false, false)) == true
    assert @dec.is_no(@dec.equivalent?(false, false)) == false
  end

  test "equivalent? of distinct Bools is a No carrying a disproof" do
    assert @dec.is_yes(@dec.equivalent?(true, false)) == false
    assert @dec.is_no(@dec.equivalent?(true, false)) == true

    assert @dec.is_yes(@dec.equivalent?(false, true)) == false
    assert @dec.is_no(@dec.equivalent?(false, true)) == true
  end

  test "a Yes tags its result and a No carries a disproof" do
    assert {:Yes, _proof} = @dec.equivalent?(true, true)
    assert {:No, _disproof} = @dec.equivalent?(true, false)
  end
end
