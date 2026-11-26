defmodule Cure.Elab.Phase5U6ErasureBackendTest do
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.{Emit, Program}

  @forbidden_atoms MapSet.new([
                     :level_type,
                     :level_value,
                     :vlevel,
                     :universe_zero,
                     :universe_succ,
                     :universe_max,
                     :UniverseLevel,
                     :TypeLimit,
                     :TypeLimit0,
                     :TypeLimit1
                   ])

  defp unwrap_error({:error, {:source_context, inner, _meta}}), do: unwrap_error({:error, inner})
  defp unwrap_error(other), do: other

  describe "U6 §13 / §18.1-2 runtime-relevant UniverseLevel rejection" do
    test "rejects explicit present/linear/affine grade on a UniverseLevel parameter" do
      for grade_src <- ["@linear", "@affine"] do
        src = """
        mod BadGrade
          fn f(#{grade_src} l: UniverseLevel) -> Int = 0
        end
        """

        assert {:error, {:runtime_relevant_level, "l", :binder}} = unwrap_error(Program.elaborate(src))
      end
    end

    test "rejects returning a UniverseLevel literal" do
      src = """
      mod BadReturnLit
        fn bad() -> UniverseLevel = universe_zero
      end
      """

      assert {:error, {:runtime_relevant_level, :level_value, :returned}} = unwrap_error(Program.elaborate(src))
    end

    test "rejects returning a UniverseLevel parameter" do
      src = """
      mod BadReturnVar
        fn bad({l: UniverseLevel}) -> UniverseLevel = l
      end
      """

      assert {:error, {:erased_used_relevantly, %{site: :returned}}} = unwrap_error(Program.elaborate(src))
    end

    test "rejects placing UniverseLevel in a present constructor field" do
      adt_src = """
      mod BadAdtBox
        type Box = MkBox(UniverseLevel)
      end
      """

      assert {:error, {:runtime_relevant_level, _, :ctor_field}} = unwrap_error(Program.elaborate(adt_src))

      gadt_src = """
      mod BadGadtBox
        type Box indices (n: Nat)
          MkBox : UniverseLevel -> Box(Z)
      end
      """

      assert {:error, {:runtime_relevant_level, _, :ctor_field}} = unwrap_error(Program.elaborate(gadt_src))
    end

    test "rejects @extern returning UniverseLevel or taking a present UniverseLevel argument" do
      ret_src = """
      mod BadExternRet
        @extern(:erlang, :self, 0)
        fn bad_ret() -> UniverseLevel
      end
      """

      assert {:error, {:runtime_relevant_level, _, :extern_return}} = unwrap_error(Program.elaborate(ret_src))

      arg_src = """
      mod BadExternArg
        @extern(:erlang, :abs, 1)
        fn bad_arg(l: UniverseLevel) -> Int
      end
      """

      assert {:error, {:extern_arity_mismatch, %{declared: 1, present: 0}}} = unwrap_error(Program.elaborate(arg_src))
    end

    test "rejects pattern matching on a UniverseLevel" do
      src = """
      mod BadMatchLevel
        fn bad({l: UniverseLevel}) -> Int =
          match l
            _ -> 0
          end
      end
      """

      assert {:error, _} = Program.elaborate(src)
    end
  end

  describe "U6 §13 / §19.5 erasure and backend invariance" do
    test "erased UniverseLevel binders drop completely from runtime arity and emitted forms" do
      src = """
      mod ErasedLevels
        use Std.List
        use Std.Option
        use Std.Sigma
        use Std.Equivalent

        type Pack indices (n: Nat)
          MkPack : {l: UniverseLevel} -> Int -> Pack(Z)

        fn poly_id({l: UniverseLevel}, {a: Type(l)}, x: a) -> a = x
        fn use_id(n: Int) -> Int = poly_id(n)
        fn unpack(p: Pack(Z)) -> Int =
          match p
            MkPack(n) -> n
        fn mk_pack(n: Int) -> Pack(Z) = MkPack(n)
        fn run() -> Int = unpack(mk_pack(use_id(42)))
      end
      """

      assert {:ok, env} = Program.elaborate(src)

      # Runtime arity of poly_id is 1 (only x), not 3.
      poly_id_def = Env.get_def(env, :"ErasedLevels#poly_id")
      assert poly_id_def.quantities == [:erased, :erased, :unrestricted]

      local_names = [
        :"ErasedLevels#poly_id",
        :"ErasedLevels#use_id",
        :"ErasedLevels#unpack",
        :"ErasedLevels#mk_pack",
        :"ErasedLevels#run"
      ]

      assert {:ok, forms} = Emit.compile_forms(env, :cure_u6_erased_levels_test, local_names)

      # Zero universe values or ops survive anywhere in the emitted Erlang abstract forms.
      assert collect_forbidden_atoms(forms) == []

      # Compile and execute on BEAM.
      assert {:ok, mod} =
               Emit.compile_and_load(env, module: :cure_u6_erased_levels_test, functions: local_names)

      try do
        assert mod.poly_id(42) == 42
        assert mod.run() == 42
      after
        :code.purge(mod)
        :code.delete(mod)
      end
    end

    test "instantiating a polymorphic function at different universe levels emits byte-equivalent Erlang forms" do
      src_zero = """
      mod InstLevel
        fn poly_id(l: UniverseLevel, {a: Type(l)}, x: a) -> a = x
        fn call_it(n: Int) -> Int = poly_id(universe_zero, n)
      end
      """

      src_succ = """
      mod InstLevel
        fn poly_id(l: UniverseLevel, {a: Type(l)}, x: a) -> a = x
        fn call_it(n: Int) -> Int = poly_id(universe_succ(universe_zero), n)
      end
      """

      assert {:ok, env0} = Program.elaborate(src_zero)
      assert {:ok, env1} = Program.elaborate(src_succ)

      names = [:"InstLevel#poly_id", :"InstLevel#call_it"]
      assert {:ok, forms0} = Emit.compile_forms(env0, :cure_u6_inst_eq, names)
      assert {:ok, forms1} = Emit.compile_forms(env1, :cure_u6_inst_eq, names)

      # Compare function forms byte-for-byte (excluding provenance attributes).
      fn_forms0 = Enum.filter(forms0, &match?({:function, _, _, _, _}, &1))
      fn_forms1 = Enum.filter(forms1, &match?({:function, _, _, _, _}, &1))
      assert fn_forms0 != []
      assert :erlang.term_to_binary(fn_forms0) == :erlang.term_to_binary(fn_forms1)
    end
  end

  defp collect_forbidden_atoms(term) when is_atom(term) do
    if MapSet.member?(@forbidden_atoms, term), do: [term], else: []
  end

  defp collect_forbidden_atoms(term) when is_tuple(term) do
    term |> Tuple.to_list() |> Enum.flat_map(&collect_forbidden_atoms/1)
  end

  defp collect_forbidden_atoms(term) when is_list(term) do
    Enum.flat_map(term, &collect_forbidden_atoms/1)
  end

  defp collect_forbidden_atoms(_other), do: []
end
