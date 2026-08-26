defmodule Cure.Stdlib.BoundedWideningTest do
  use ExUnit.Case, async: true
  use ExUnitProperties

  alias Cure.Core.Env

  @runtime_source """
  mod BoundedWideningRuntime
    use Std.Bounded

    fn widen_3_by_2(value: Bounded(3)) -> Bounded(plus(3, 2)) = widen(value)
    fn inject_left_3_2(value: Bounded(3)) -> Bounded(plus(3, 2)) = inject_left(value)
    fn inject_right_3_2(value: Bounded(2)) -> Bounded(plus(3, 2)) = inject_right(3, value)
    fn split_3_2(value: Bounded(plus(3, 2))) -> BoundedSum(3, 2) = split_sum(3, value)
  """

  @proof_source """
  mod BoundedWideningProofs
    use Std.Bounded
    use Std.Equivalent
  """

  setup_all do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@runtime_source, emit_events: false)
    {:ok, runtime_module: module}
  end

  test "widening preserves every source value and keeps it in range", %{runtime_module: module} do
    assert Enum.map(0..2, &apply(module, :widen_3_by_2, [&1])) == [0, 1, 2]
  end

  test "left and right injections are disjoint and cover the combined range", %{runtime_module: module} do
    left = Enum.map(0..2, &apply(module, :inject_left_3_2, [&1]))
    right = Enum.map(0..1, &apply(module, :inject_right_3_2, [&1]))

    assert left == [0, 1, 2]
    assert right == [3, 4]
    assert MapSet.disjoint?(MapSet.new(left), MapSet.new(right))
    assert Enum.sort(left ++ right) == Enum.to_list(0..4)
  end

  test "splitting the combined range recovers the exact injection side and value", %{
    runtime_module: module
  } do
    assert Enum.map(0..4, &apply(module, :split_3_2, [&1])) == [
             {:BoundedLeft, 0},
             {:BoundedLeft, 1},
             {:BoundedLeft, 2},
             {:BoundedRight, 0},
             {:BoundedRight, 1}
           ]
  end

  test "widening and both injections are kernel-checked and certified total" do
    assert {:ok, env} = Cure.Elab.Program.elaborate(@proof_source)

    for name <- [
          :"Std.Bounded#widen",
          :"Std.Bounded#inject_left",
          :"Std.Bounded#inject_right",
          :"Std.Bounded#split_sum",
          :"Std.Bounded#fold_sum"
        ] do
      assert Env.get_def(env, name)
      assert Env.certified?(env, name)
    end

    assert Env.get_def(env, :"Std.Bounded#split_injected_left")
    assert Env.get_def(env, :"Std.Bounded#split_injected_right")
  end

  test "erasure drops every index while retaining the right injection's runtime offset" do
    {:ok, set} =
      Cure.Compiler.Artifacts.open_verified_set(
        kind: :stdlib,
        candidates: Cure.Stdlib.Paths.beam_dirs()
      )

    artifact =
      set.modules["Std.Bounded"].artifacts
      |> Enum.find(&(&1.module == "Cure.Std.Bounded"))

    beam = File.read!(Path.join(set.artifact_root, artifact.path))
    {:beam_file, :"Cure.Std.Bounded", exports, _attrs, _info, _functions} = :beam_disasm.file(beam)

    assert Enum.any?(exports, &match?({:widen, 1, _}, &1))
    assert Enum.any?(exports, &match?({:inject_left, 1, _}, &1))
    assert Enum.any?(exports, &match?({:inject_right, 2, _}, &1))
    assert Enum.any?(exports, &match?({:split_sum, 2, _}, &1))
    assert Enum.any?(exports, &match?({:fold_sum, 3, _}, &1))
    refute Enum.any?(exports, &match?({:inject_right, 3, _}, &1))
  end

  property "widening and sum injections preserve range and side for generated bounds" do
    check all(
            left_bound <- integer(1..64),
            right_bound <- integer(1..64),
            left_value <- integer(0..(left_bound - 1)),
            right_value <- integer(0..(right_bound - 1)),
            max_runs: 50
          ) do
      module = :"Cure.Std.Bounded"
      widened = apply(module, :widen, [left_value])
      left = apply(module, :inject_left, [left_value])
      right = apply(module, :inject_right, [left_bound, right_value])
      combined_bound = left_bound + right_bound

      assert widened == left_value
      assert left == left_value
      assert left >= 0 and left < left_bound
      assert right == left_bound + right_value
      assert right >= left_bound and right < combined_bound
      refute left == right
    end
  end
end
