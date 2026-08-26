defmodule Cure.Stdlib.OpticDynamicRunTest do
  @moduledoc """
  The `Std.Dynamic` case affines: one `Affine(Dynamic, T)` per constructor of the
  typed-`Any` sum. Narrowing a `Dynamic` to a concrete leaf is an *affine* — it
  may miss — never a cast: `preview` yields `Some(focus)` when the tag matches and
  `None` when it does not, and `set`/`over` rebuild the same-tagged `Dynamic`,
  leaving a mis-tagged value untouched (the statically-kinded replacement for a
  runtime `is_integer`/`is_map` guess over an opaque `Any`).

  These ride the same GADT `Optic(s, a, k)` machinery as tuple lenses, so this
  test also pins that the cross-module `Std.Optic`←`Std.Dynamic` lowering works.
  Implicits erase, so runtime arities are `dyn_int/0`, `preview/2`, `set/3`,
  `over/3`; Option lowers OTP-lowercase (`{:some, v}` / `:none`), while `Dynamic`
  constructors stay PascalCase-tagged (`{:Int, 5}`).
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.{Program, Emit}

  setup_all do
    # Optic module: the case affines and eliminators.
    osrc = File.read!("lib/std/optic.cure")
    {:ok, otokens} = Lexer.tokenize(osrc, emit_events: false)
    {:ok, oast} = Parser.parse(otokens, emit_events: false)
    {:ok, oenv} = Program.elaborate(osrc)
    oorigins = Program.import_origins(oast)

    ofns =
      Program.reachable_def_names(oenv, [
        :dyn_atom,
        :dyn_int,
        :dyn_float,
        :dyn_str,
        :dyn_list,
        :dyn_tuple,
        :dyn_map,
        :preview,
        :set,
        :over
      ])

    {:ok, m} =
      Emit.compile_and_load(oenv,
        module: :"Cure.Test.OpticDynamic",
        functions: ofns,
        origins: oorigins
      )

    # Dynamic module: the smart constructors that build the Dynamic values under
    # test. Compiled separately, but the runtime reps are shared (PascalCase
    # tagged tuples), so the values flow straight into the optic affines.
    dsrc = File.read!("lib/std/dynamic.cure")
    {:ok, denv} = Program.elaborate(dsrc)
    dfns = Program.reachable_def_names(denv, [:of_int, :of_str, :of_list, :of_map, :entry])
    {:ok, d} = Emit.compile_and_load(denv, module: :"Cure.Test.OpticDynBuild", functions: dfns)

    {:ok, m: m, d: d}
  end

  test "preview hits the matching tag and misses every other", %{m: m, d: d} do
    di = apply(m, :dyn_int, [])
    assert apply(m, :preview, [di, apply(d, :of_int, [5])]) == {:some, 5}
    assert apply(m, :preview, [di, apply(d, :of_str, [~c"x"])]) == :none
  end

  test "set rebuilds a same-tagged Dynamic and no-ops on a mismatch", %{m: m, d: d} do
    di = apply(m, :dyn_int, [])
    # focus present → replace, keeping the Dynamic shape
    assert apply(m, :set, [di, 9, apply(d, :of_int, [5])]) == {:Int, 9}
    # focus absent → structure untouched (affine set is a no-op on a miss)
    other = apply(d, :of_str, [~c"x"])
    assert apply(m, :set, [di, 9, other]) == other
  end

  test "over modifies the focus in place through the affine", %{m: m, d: d} do
    di = apply(m, :dyn_int, [])
    assert apply(m, :over, [di, fn n -> n + 1 end, apply(d, :of_int, [5])]) == {:Int, 6}
  end

  test "dyn_str narrows a string leaf", %{m: m, d: d} do
    ds = apply(m, :dyn_str, [])
    assert apply(m, :preview, [ds, apply(d, :of_str, [~c"hi"])]) == {:some, ~c"hi"}
    assert apply(m, :preview, [ds, apply(d, :of_int, [1])]) == :none
  end

  test "dyn_map narrows a heterogeneous association list", %{m: m, d: d} do
    # Map([ Entry(Str("n"), Int(1)), Entry(Str("s"), Str("x")) ]) — mixed
    # value types under one Dynamic; dyn_map focuses the whole entry list.
    e1 = apply(d, :entry, [apply(d, :of_str, [~c"n"]), apply(d, :of_int, [1])])
    e2 = apply(d, :entry, [apply(d, :of_str, [~c"s"]), apply(d, :of_str, [~c"x"])])
    doc = apply(d, :of_map, [[e1, e2]])

    dm = apply(m, :dyn_map, [])
    assert apply(m, :preview, [dm, doc]) == {:some, [e1, e2]}

    # a non-map Dynamic has no map focus
    assert apply(m, :preview, [dm, apply(d, :of_int, [0])]) == :none
  end
end
