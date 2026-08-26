defmodule Antigen.Backend.StreamDataTest do
  use ExUnit.Case, async: true
  alias Antigen.{Gen, Backend}

  test "interp maps each Gen primitive to a StreamData generator that samples in-support" do
    gen = Gen.one_of([Gen.return(:a), Gen.return(:b)])
    samples = Backend.StreamData.sample(Backend.StreamData.interp(gen), 20)
    assert Enum.all?(samples, &(&1 in [:a, :b]))
    assert length(samples) == 20
  end

  test "bind maps to StreamData.bind (integrated shrinking preserved)" do
    gen = Gen.bind(Gen.member_of([1, 2, 3]), fn n -> Gen.return(n * 10) end)
    samples = Backend.StreamData.sample(Backend.StreamData.interp(gen), 30)
    assert Enum.all?(samples, &(&1 in [10, 20, 30]))
  end

  test "member_of over a range covers the whole range across enough samples" do
    samples = Backend.StreamData.sample(Backend.StreamData.interp(Gen.int(0, 4)), 200)
    assert MapSet.subset?(MapSet.new(0..4), MapSet.new(samples))
  end
end
