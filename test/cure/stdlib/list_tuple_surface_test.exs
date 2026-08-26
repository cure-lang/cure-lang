defmodule Cure.Stdlib.ListTupleSurfaceTest do
  # uncons is Idris/Haskell `Maybe (a, List a)` — the empty case is None, not the
  # type-incoherent `%[[],[]]` the classic untyped `Tuple` allowed. This makes the
  # whole Std.List module elaborate on the DEPENDENT pipeline (previously it died at
  # uncons's `%[h,t]` : bare undefined `Tuple` -> unsupported_expression).
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "Std.List elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/list.cure"))
  end

  test "uncons returns Some(%[h, t]) / None and runs" do
    src = """
    mod M
      use Std.List
      use Std.Option
      fn head_or(xs: List(Int), d: Int) -> Int =
        match Std.List.uncons(xs)
          Some(p) -> p.1
          None()  -> d
    """

    assert {:ok, env} = Program.elaborate(src)
    # Qualified calls use the ordinary Std.List runtime module; an importing
    # module must never re-emit the provider's implementation locally.
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.M", functions: [:head_or])
    assert apply(m, :head_or, [[5, 6, 7], 0]) == 5
    assert apply(m, :head_or, [[], 0]) == 0
  end
end
