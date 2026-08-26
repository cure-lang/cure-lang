defmodule Antigen.Generators.PrimitiveTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.{Primitive, SigMenu}
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.Challenge
  alias Cure.Core.{Context, Kernel, Normalise}

  defp ctx, do: SigMenu.rebuild_context(SigMenu.env_of(:v1), [])

  @sample 400
  @sample_seed 20_260_724

  defp sample, do: B.sample_seeded(Primitive.gen(), @sample, @sample_seed)

  # K2 (spec 2026-07-09): the generator emits builtin-op GLOBAL spines, not
  # {:prim} nodes. The op is the spine's head global name. A1 (spec 2026-07-09
  # §1-A) adds the polymorphic struct_eq/struct_ne op: a saturated spine carries
  # a leading TYPE-witness argument, so it is a 3-arg application, not 2; an
  # under-saturated struct_eq/struct_ne (type witness only) is structurally the
  # same 1-arg shape as an ordinary unop and already matched below.
  defp spine?({:app, {:app, {:app, {:global, _g}, _ty}, _a}, _b}), do: true
  defp spine?({:app, {:app, {:global, _g}, _a}, _b}), do: true
  defp spine?({:app, {:global, _g}, _a}), do: true
  defp spine?(_), do: false

  defp op_of({:app, {:app, {:app, {:global, g}, _ty}, _a}, _b}), do: g
  defp op_of({:app, {:app, {:global, g}, _a}, _b}), do: g
  defp op_of({:app, {:global, g}, _a}), do: g

  test "every sampled builtin-op challenge is a well-typed :typed_term over v1" do
    for %Challenge{} = c <- sample() do
      assert c.kind == :typed_term
      assert c.assay in Antigen.Generators.Term.assay_ids()
      assert c.payload.sig == :v1
      assert c.payload.ctx == []

      assert spine?(c.payload.term),
             "expected a builtin-op global spine, got #{inspect(c.payload.term)}"

      cx = ctx()

      case Kernel.infer(cx, c.payload.term) do
        {:ok, inferred} ->
          # the claimed type is exactly the inferred type
          assert Normalise.quote(inferred, Context.length(cx)) == c.payload.type
          # and it normalizes without fuel exhaustion (exercises the certified-δ
          # builtin-op fold)
          assert Normalise.nf(cx, c.payload.term, fuel: 500_000, delta: :certified) !=
                   :fuel_exhausted

        other ->
          flunk("builtin-op term failed to infer: #{inspect(c.payload.term)} -> #{inspect(other)}")
      end
    end
  end

  test "the sample exercises every arithmetic op and both numeric types" do
    sample = sample()

    ops = sample |> Enum.map(fn c -> op_of(c.payload.term) end) |> MapSet.new()

    for op <- [:int_add, :int_sub, :int_mul, :int_div, :int_rem, :int_neg],
        do: assert(op in ops, "op #{op} never generated")

    for op <- [:float_add, :float_sub, :float_mul, :float_div, :float_neg],
        do: assert(op in ops, "op #{op} never generated")

    types = sample |> Enum.map(fn c -> c.payload.type end) |> MapSet.new()
    assert {:data, :Int, [], []} in types
    assert {:float_type} in types
  end

  test "the sample exercises Bool-returning numeric comparisons" do
    sample = sample()

    ops = sample |> Enum.map(fn c -> op_of(c.payload.term) end) |> MapSet.new()

    for op <- [:int_lt, :int_le, :int_gt, :int_ge, :int_eq, :int_ne],
        do: assert(op in ops, "op #{op} never generated")

    for op <- [:float_lt, :float_le, :float_gt, :float_ge, :float_eq, :float_ne],
        do: assert(op in ops, "op #{op} never generated")

    # at least one challenge claims the Bool type
    assert Enum.any?(sample, fn c -> c.payload.type == {:data, :Bool, [], []} end)

    # connectives (:and/:or/:not) are Std.Bool case-defs — the generator must
    # NOT emit spines headed by them
    refute Enum.any?(sample, fn c -> op_of(c.payload.term) in [:and, :or, :not] end)
  end

  test "the sample includes at least one stuck (zero-divisor) op spine" do
    sample = sample()

    assert Enum.any?(sample, fn c ->
             match?(
               {:app, {:app, {:global, g}, _}, {:int_lit, 0}} when g in [:int_div, :int_rem],
               c.payload.term
             )
           end),
           "no zero-divisor spine generated (needed to hit the fold's :stuck clauses)"
  end
end
