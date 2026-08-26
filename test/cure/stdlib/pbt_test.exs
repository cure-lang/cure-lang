defmodule Cure.Stdlib.PbtTest do
  use ExUnit.Case, async: false

  # `Cure.Std.Gen` and `Cure.Std.Test` are loaded dynamically by
  # `Cure.Stdlib.Preload` in `setup_all` below; Elixir's compile-time
  # checker doesn't see them, so silence the otherwise correct "module
  # not available" warnings.
  @compile {:no_warn_undefined, [:"Cure.Std.Gen", :"Cure.Std.Test"]}

  setup_all do
    Cure.Stdlib.Preload.preload(examples: false, kind: :all)
    :ok
  end

  describe "Std.Gen basics" do
    test "int_in/2 stays within [lo, hi]" do
      for _ <- 1..50 do
        n = :"Cure.Std.Gen".int_in(10, 20)
        assert n >= 10
        assert n <= 20
      end
    end

    test "bool/0 returns a boolean" do
      sample = for _ <- 1..50, do: :"Cure.Std.Gen".bool()
      assert Enum.all?(sample, &is_boolean/1)
      assert Enum.any?(sample, &(&1 == true))
      assert Enum.any?(sample, &(&1 == false))
    end

    test "list_int/3 produces a list within length bound and element range" do
      for _ <- 1..20 do
        xs = :"Cure.Std.Gen".list_int(5, 0, 100)
        assert is_list(xs)
        assert length(xs) <= 5
        Enum.each(xs, fn v -> assert v >= 0 and v <= 100 end)
      end
    end
  end

  describe "Std.Test.forall" do
    test "passes when property holds on every sample" do
      # forall(gen, property, runs) -> :ok when property never fails.
      # `n + 0 == n` is trivially true for any Int.
      gen = fn _ -> :"Cure.Std.Gen".int_in(-1_000, 1_000) end
      property = fn n -> n + 0 == n end
      assert :"Cure.Std.Test".forall(gen, property, 50) == :unit
    end

    test "raises when property is false at some sample" do
      gen = fn _ -> :"Cure.Std.Gen".int_in(0, 0) end
      # property fails at 0 -> expect error raised
      property = fn _ -> false end

      assert_raise ErlangError, fn ->
        :"Cure.Std.Test".forall(gen, property, 5)
      end
    end
  end
end
