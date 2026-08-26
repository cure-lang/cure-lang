defmodule Cure.Stdlib.ListIndexAffineTest do
  @moduledoc """
  `Std.Optic.ix/1`: the list-index affine. A bare `List` carries no length, so
  indexing genuinely may miss — `ix` is an AFFINE, not a lens. `preview` is
  `Some` in range and `None` out of range or on `[]`; `set`/`over` replace in
  place when the index exists and are a NO-OP otherwise (the miss-is-a-no-op
  affine law). Built on `Std.List.at`/`set_at`. Option lowers OTP-lowercase
  (`{:some, v}` / `:none`); implicits erase, so runtime arities are `ix/1`,
  `preview/2`, `set/3`, `over/3`, `compose/2`.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  setup_all do
    src = File.read!("lib/std/optic.cure")
    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [:ix, :preview, :set, :over, :compose])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.Test.ListIndexAffine", functions: fns)
    {:ok, m: m}
  end

  test "preview hits in range, misses out of range and on []", %{m: m} do
    o = apply(m, :ix, [1])
    assert apply(m, :preview, [o, [10, 20, 30]]) == {:some, 20}
    assert apply(m, :preview, [o, [10]]) == :none
    assert apply(m, :preview, [o, []]) == :none
  end

  test "set replaces in range and no-ops out of range", %{m: m} do
    o = apply(m, :ix, [1])
    assert apply(m, :set, [o, 99, [10, 20, 30]]) == [10, 99, 30]
    assert apply(m, :set, [o, 99, [10]]) == [10]
  end

  test "over modifies in range and no-ops out of range", %{m: m} do
    o = apply(m, :ix, [0])
    assert apply(m, :over, [o, fn n -> n + 1 end, [10, 20]]) == [11, 20]
    assert apply(m, :over, [o, fn n -> n + 1 end, []]) == []
  end

  test "affine laws hold on a sample (preview-set, set-preview, set-set)", %{m: m} do
    o = apply(m, :ix, [2])
    xs = [1, 2, 3, 4]
    # preview-set: writing the currently-focused value back is identity
    {:some, cur} = apply(m, :preview, [o, xs])
    assert apply(m, :set, [o, cur, xs]) == xs
    # set-preview: after `set v`, the focus previews back as `Some(v)`
    assert apply(m, :preview, [o, apply(m, :set, [o, 42, xs])]) == {:some, 42}
    # set-set: the last write wins
    assert apply(m, :set, [o, 7, apply(m, :set, [o, 5, xs])]) == apply(m, :set, [o, 7, xs])
  end

  test "compose(ix, ix) reaches into a nested list and no-ops on an inner miss", %{m: m} do
    o = apply(m, :compose, [apply(m, :ix, [0]), apply(m, :ix, [1])])
    assert apply(m, :preview, [o, [[1, 2, 3], [4, 5]]]) == {:some, 2}
    assert apply(m, :set, [o, 99, [[1, 2, 3], [4, 5]]]) == [[1, 99, 3], [4, 5]]
    # inner index out of range → whole set is a no-op
    assert apply(m, :set, [o, 99, [[1], [4, 5]]]) == [[1], [4, 5]]
  end
end
