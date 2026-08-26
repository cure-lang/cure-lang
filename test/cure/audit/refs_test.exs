defmodule Cure.Audit.RefsTest do
  use ExUnit.Case, async: true
  alias Cure.Audit.Refs

  test "collects globals from every child position" do
    t = {:app, {:global, :f}, {:global, :g}}
    assert Refs.globals(t) == [:f, :g]
  end

  test "collects globals inside a let — the clause global_refs/1 lacks" do
    t = {:let, :unrestricted, {:global, :ty}, {:global, :val}, {:global, :body}}
    assert Refs.globals(t) == [:body, :ty, :val]
  end

  test "collects globals from case scrutinee, motive, and branches" do
    t = {:case, {:global, :s}, {:global, :m}, [{:Cons, 2, {:global, :b}}]}
    assert Refs.globals(t) == [:b, :m, :s]
  end

  test "collects globals from data params and indices, and ctor args" do
    t = {:data, :Vec, [{:global, :p}], [{:global, :i}]}
    assert Refs.globals(t) == [:i, :p]
    assert Refs.globals({:ctor, :Cons, [{:global, :x}]}) == [:x]
  end

  test "deduplicates and sorts" do
    t = {:app, {:global, :f}, {:app, {:global, :f}, {:global, :a}}}
    assert Refs.globals(t) == [:a, :f]
  end

  test "reports holes and absurd" do
    t = {:app, {:hole, "goal"}, {:absurd}}
    assert Refs.scan(t) == %{globals: [], families: [], holes: ["goal"], absurd: 1}
  end

  test "accepts the extern body sentinel" do
    assert Refs.scan({:extern, {:erlang, :length, 1}}) ==
             %{globals: [], families: [], holes: [], absurd: 0}
  end

  test "accepts nil — a builtin op's absent body" do
    # Every `builtin_op`-tagged def (`Builtins.seed_ops`) has `body: nil`, not a
    # Core.Term. Ledger's reachability walk does not skip them, so without this
    # clause every audit of a module using arithmetic raises
    # `unknown Core term in Audit.Refs: nil`.
    assert Refs.scan(nil) == %{globals: [], families: [], holes: [], absurd: 0}
  end

  test "collects globals inside an effect type" do
    assert Refs.globals({:effect_type, {:global, :Result}}) == [:Result]
  end

  test "raises on an unknown node instead of silently returning []" do
    assert_raise ArgumentError, ~r/unknown Core term/, fn -> Refs.scan({:bogus}) end
  end

  test "every term Antigen generates walks without raising" do
    # Antigen already generates well-formed Core terms. This guard upgrades
    # automatically as the Core grammar grows: a new former that Refs does not
    # handle makes this test raise.
    #
    # `default_gen/0` yields `%Antigen.Challenge{}` envelopes, not bare terms —
    # the Core terms live at `payload.term`, `payload.type`, and `payload.ctx`.
    # Refs must NOT learn to walk a Challenge; that would be the catch-all this
    # module exists to refuse.
    challenges =
      Antigen.Backend.StreamData.sample_seeded(
        Antigen.Generators.Term.default_gen(),
        200,
        20_260_710
      )

    terms =
      Enum.flat_map(challenges, fn %Antigen.Challenge{payload: p} ->
        [p[:term], p[:type]] ++ List.wrap(p[:ctx])
      end)
      |> Enum.reject(&is_nil/1)

    refute terms == [], "generator produced no Core terms; the guard would be vacuous"

    for t <- terms do
      assert is_map(Refs.scan(t))
    end
  end
end
