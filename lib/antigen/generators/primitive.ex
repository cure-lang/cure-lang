defmodule Antigen.Generators.Primitive do
  @moduledoc """
  Structure-directed generator for **primitive arithmetic** Core terms — now
  registry-keyed builtin-op GLOBAL spines (K2, spec 2026-07-09; the `{:prim}`
  node is retired). The reachability lever for the certified-δ literal
  acceleration (`Normalise.builtin_op_fold` → the audited `Eval.fold/2` table)
  and the ordinary global-Pi typing path — Int/Float surfaces the mode-directed
  `Generators.Term` machinery never emits (its goal menu has no Int/Float
  types, spec §5).

  Every generated term is well-typed **by construction** over the v1 signature
  (which seeds the 25 ops) in the empty context: operands are
  `:int_lit`/`:float_lit` literals (or shallow nested spines of the same
  numeric type), and the claimed `type` is exactly the op's result type
  (`{:data, :Int, [], []}` post-flip / `{:float_type}`, comparisons `Bool`). div/rem occasionally
  draw a **zero divisor**, which the kernel types fine but the fold leaves
  *stuck* (the spine stays a neutral `napp` chain) — this exercises the
  §G.1 partial-op rule.

  Emits **numeric** ops (monomorphic twins `int_add/…/int_rem`,
  `float_add/…/float_div`, `int_neg`/`float_neg` — no `float_rem`, it does not
  exist) and **numeric comparisons** (`int_lt/…/int_ne`, `float_lt/…/float_ne`,
  result `Bool` via the `:bool` builtin). The Boolean **connectives**
  (`and/or/not`) and Bool-operand `eq/ne` are deliberately NOT emitted: they
  are Std.Bool `case`-defs, covered through the elaborator's lowering.

  Tagged for the three infer+normalize assays (`infer_check`,
  `subject_reduction`, `normalization`); `normalization` is the one that
  drives `nf` — hence the certified-δ hook — hence `fold`.
  """
  alias Antigen.{Gen, Challenge}

  # Numeric-result assays only — every one runs `infer` then `nf` on the term,
  # which is the path through the builtin-op fold. (erasure_preservation is
  # omitted: its value here is marginal and it is the one assay that does not
  # add fold coverage.)
  @assays ["term/infer_check", "term/subject_reduction", "term/normalization"]

  @lit_range 20
  @max_depth 2

  @bool_type {:data, :Bool, [], []}
  @int_cmp_ops [:int_lt, :int_le, :int_gt, :int_ge, :int_eq, :int_ne]
  @float_cmp_ops [:float_lt, :float_le, :float_gt, :float_ge, :float_eq, :float_ne]
  @struct_ops [:struct_eq, :struct_ne]

  @spec gen(keyword()) :: Gen.t()
  def gen(_opts \\ []) do
    Gen.bind(Gen.member_of(@assays), fn assay ->
      Gen.bind(prim_gen(), fn {term, type} ->
        Gen.return(
          Challenge.new(
            kind: :typed_term,
            assay: assay,
            label: :well_typed,
            payload: %{sig: :v1, ctx: [], type: type, term: term},
            note: "primitive arithmetic (builtin-op global spines)"
          )
        )
      end)
    end)
  end

  # -- op spine + its result type ---------------------------------------------
  defp prim_gen do
    Gen.frequency([
      {5, Gen.bind(int_prim(@max_depth), fn t -> Gen.return({t, {:data, :Int, [], []}}) end)},
      {4, Gen.bind(float_prim(@max_depth), fn t -> Gen.return({t, {:float_type}}) end)},
      {5, Gen.bind(bool_prim(@max_depth), fn t -> Gen.return({t, @bool_type}) end)},
      {2, struct_eq_int()},
      {2, struct_eq_float()},
      {1, struct_eq_partial()}
    ])
  end

  # -- A1 struct_eq/struct_ne (polymorphic structural equality) ---------------
  # `struct_eq/struct_ne : Pi(a:Type0). a -> a -> Bool` (Cure.Core.Builtins
  # seed_struct_ops). A FULLY saturated 3-arg spine (type witness + two literal
  # operands) is the reachability lever for `Normalise.builtin_op_fold`'s
  # `[_tyval, l, r]` struct-op arm — it folds via the SAME audited `Eval.fold`
  # table when both operands whnf to int/float literals (Amendment A1, spec
  # 2026-07-09 §1-A).
  defp struct_eq_int do
    Gen.bind(Gen.member_of(@struct_ops), fn g ->
      Gen.bind(int_lit(), fn a ->
        Gen.bind(int_lit(), fn b ->
          Gen.return({{:app, {:app, {:app, {:global, g}, {:data, :Int, [], []}}, a}, b}, @bool_type})
        end)
      end)
    end)
  end

  defp struct_eq_float do
    Gen.bind(Gen.member_of(@struct_ops), fn g ->
      Gen.bind(float_lit(), fn a ->
        Gen.bind(float_lit(), fn b ->
          Gen.return({{:app, {:app, {:app, {:global, g}, {:float_type}}, a}, b}, @bool_type})
        end)
      end)
    end)
  end

  # An UNDER-saturated struct_eq/struct_ne spine (the type witness only, no
  # operands yet) — a legitimate partial application (its type is the residual
  # `a -> a -> Bool` Pi), but its argument count (1) matches neither the 3-arg
  # struct-op clause NOR the generic op clause (whose guard excludes struct_eq/
  # struct_ne outright) — the reachability lever for `builtin_op_fold`'s final
  # wrong-arity catch-all (§ "A struct op at the wrong arity" — never unsound,
  # at worst a missed fold; the spine just stays neutral/stuck).
  defp struct_eq_partial do
    Gen.bind(Gen.member_of(@struct_ops), fn g ->
      Gen.bind(Gen.member_of([{:int_type}, {:float_type}]), fn ty ->
        Gen.return(
          {{:app, {:global, g}, ty},
           {:pi, Cure.Core.Grade.unrestricted(), ty, {:pi, Cure.Core.Grade.unrestricted(), ty, @bool_type}}}
        )
      end)
    end)
  end

  # -- Int ops ------------------------------------------------------------------
  defp int_prim(depth) do
    Gen.frequency([
      {2, binop(:int_add, &int_operand/1, depth)},
      {2, binop(:int_sub, &int_operand/1, depth)},
      {2, binop(:int_mul, &int_operand/1, depth)},
      {2, divop(:int_div, &int_operand/1, int_zero(), depth)},
      {2, divop(:int_rem, &int_operand/1, int_zero(), depth)},
      {1, unop(:int_neg, &int_operand/1, depth)}
    ])
  end

  defp int_operand(0), do: int_lit()

  defp int_operand(depth) do
    Gen.frequency([{4, int_lit()}, {1, int_prim(depth - 1)}])
  end

  defp int_lit, do: Gen.bind(Gen.int(-@lit_range, @lit_range), fn n -> Gen.return({:int_lit, n}) end)
  defp int_zero, do: Gen.return({:int_lit, 0})

  # -- Float ops (no float_rem — remainder is Int-only) -------------------------
  defp float_prim(depth) do
    Gen.frequency([
      {2, binop(:float_add, &float_operand/1, depth)},
      {2, binop(:float_sub, &float_operand/1, depth)},
      {2, binop(:float_mul, &float_operand/1, depth)},
      {2, divop(:float_div, &float_operand/1, float_zero(), depth)},
      {1, unop(:float_neg, &float_operand/1, depth)}
    ])
  end

  defp float_operand(0), do: float_lit()

  defp float_operand(depth) do
    Gen.frequency([{4, float_lit()}, {1, float_prim(depth - 1)}])
  end

  defp float_lit,
    do: Gen.bind(Gen.int(-@lit_range, @lit_range), fn n -> Gen.return({:float_lit, n / 4}) end)

  defp float_zero, do: Gen.return({:float_lit, 0.0})

  # -- Bool-returning comparisons ----------------------------------------------
  # Monomorphic numeric comparisons (int_* over Int operands, float_* over
  # Float), result Bool. Connectives and Bool-operand eq/ne are intentionally
  # excluded (Std.Bool case-defs) — see the moduledoc.
  defp bool_prim(depth) do
    Gen.frequency(
      Enum.map(@int_cmp_ops, fn g -> {1, binop(g, &int_operand/1, depth)} end) ++
        Enum.map(@float_cmp_ops, fn g -> {1, binop(g, &float_operand/1, depth)} end)
    )
  end

  # -- op shapes (builtin-op global spines) --------------------------------------
  defp binop(g, operand, depth) do
    Gen.bind(operand.(depth), fn a ->
      Gen.bind(operand.(depth), fn b ->
        Gen.return({:app, {:app, {:global, g}, a}, b})
      end)
    end)
  end

  # A binary op whose right operand is occasionally a zero literal (stuck fold).
  defp divop(g, operand, zero_gen, depth) do
    Gen.bind(operand.(depth), fn a ->
      Gen.bind(Gen.frequency([{6, operand.(depth)}, {1, zero_gen}]), fn b ->
        Gen.return({:app, {:app, {:global, g}, a}, b})
      end)
    end)
  end

  defp unop(g, operand, depth) do
    Gen.bind(operand.(depth), fn a -> Gen.return({:app, {:global, g}, a}) end)
  end
end
