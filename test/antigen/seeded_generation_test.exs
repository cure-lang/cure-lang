defmodule Antigen.SeededGenerationTest do
  @moduledoc """
  Reproducible `mix antigen` runs by seed. Every draw threads an integer master
  seed so a run can be replayed exactly with `--seed N`. Covers the core seeded
  primitive (`Backend.StreamData.sample_seeded/3`), the per-round seed derivation
  used under `--bias`, and end-to-end reproducibility through `Runner.generate/1`.
  """
  use ExUnit.Case, async: true
  import ExUnit.CaptureIO
  alias Antigen.{Backend.StreamData, Runner}

  @tmp "tmp/antigen_seeded_generation_test"

  setup do
    File.rm_rf!(@tmp)
    File.mkdir_p!(@tmp)
    on_exit(fn -> File.rm_rf!(@tmp) end)
    :ok
  end

  describe "Backend.StreamData.sample_seeded/3" do
    @descr {:member_of, Enum.to_list(1..100)}

    test "same seed yields an identical sequence of the requested length" do
      a = StreamData.sample_seeded(@descr, 200, 12_345)
      b = StreamData.sample_seeded(@descr, 200, 12_345)

      assert a == b
      assert length(a) == 200
    end

    test "different seeds yield different sequences" do
      a = StreamData.sample_seeded(@descr, 200, 12_345)
      c = StreamData.sample_seeded(@descr, 200, 999)

      refute a == c
    end

    test "count of 0 yields an empty list" do
      assert StreamData.sample_seeded(@descr, 0, 7) == []
    end
  end

  describe "Runner.round_seed/2" do
    test "is deterministic and index-sensitive" do
      assert Runner.round_seed(42, 0) == Runner.round_seed(42, 0)
      refute Runner.round_seed(42, 0) == Runner.round_seed(42, 1)
      refute Runner.round_seed(42, 0) == Runner.round_seed(43, 0)
    end
  end

  describe "Runner.generate/1 reproducibility" do
    @gen Antigen.Generators.Totality.gen()

    test "returns the resolved seed and reproduces the seed file across runs" do
      t1 = Path.join(@tmp, "a.sexp")
      t2 = Path.join(@tmp, "b.sexp")

      r1 = Runner.generate(gen: @gen, count: 100, seeds_path: t1, seed: 7)
      r2 = Runner.generate(gen: @gen, count: 100, seeds_path: t2, seed: 7)

      assert r1.seed == 7
      assert r2.seed == 7
      assert File.read!(t1) == File.read!(t2)
    end

    test "a fresh (unseeded) run reports the seed it chose" do
      t = Path.join(@tmp, "c.sexp")
      r = Runner.generate(gen: @gen, count: 20, seeds_path: t)

      assert is_integer(r.seed)
    end
  end

  describe "mix antigen generate --seed" do
    test "prints the seed and reproduces the seed file when replayed" do
      t1 = Path.join(@tmp, "cli1.sexp")
      t2 = Path.join(@tmp, "cli2.sexp")

      out1 =
        capture_io(fn ->
          Mix.Tasks.Antigen.run(["generate", "--seed", "424242", "--count", "80", "--seeds", t1])
        end)

      out2 =
        capture_io(fn ->
          Mix.Tasks.Antigen.run(["generate", "--seed", "424242", "--count", "80", "--seeds", t2])
        end)

      assert out1 =~ "seed=424242"
      assert out2 =~ "seed=424242"
      assert File.read!(t1) == File.read!(t2)
    end

    test "prints the shape-coverage manifest report inline" do
      t = Path.join(@tmp, "cov.sexp")

      out =
        capture_io(fn ->
          Mix.Tasks.Antigen.run(["generate", "--seed", "1", "--count", "40", "--seeds", t])
        end)

      assert out =~ "shape-coverage"
    end
  end
end
