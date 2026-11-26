defmodule Cure.Elab.Phase5SigmaContextTest do
  use ExUnit.Case, async: true

  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Program

  test "a nested Sigma preserves implicit arguments from the preceding telescope" do
    source = """
    mod SigmaAnnotationContext
      type Shape = UnitShape
      type Compilation indices (shape: Shape)
        EmptyCompilation : Compilation(UnitShape)
        BoundaryCompilation : Nat -> Compilation(UnitShape)
      @reducible
      fn tag({shape: Shape}, compilation: Compilation(shape)) -> Nat = match compilation
        EmptyCompilation() -> Z()
        BoundaryCompilation(value) -> S(value)
      type Machine indices (tag: Nat)
        EmptyMachine : Machine(Z())
        BoundaryMachine : (tag: Nat) -> Machine(S(tag))
      @reducible
      fn machine({shape: Shape}, compilation: Compilation(shape)) -> Machine(tag(compilation)) = match compilation
        EmptyCompilation() -> EmptyMachine()
        BoundaryCompilation(value) -> BoundaryMachine(value)
      type Path(tag: Nat, machine: Machine(tag)) indices ()
        MkPath : Path(tag, machine)
      fn inspect_nested({shape: Shape}, compilation: Compilation(shape), packed: Sigma(destination: Nat, Path(tag(compilation), machine(compilation)))) -> Nat = match compilation
        EmptyCompilation() -> match packed
          mk_pair(_, path) -> match path
            MkPath() -> Z()
        BoundaryCompilation(value) -> match packed
          mk_pair(_, path) -> match path
            MkPath() -> S(value)
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def_type(env, :"SigmaAnnotationContext#inspect_nested")
    assert :ok = Kernel.check_def(env, :"SigmaAnnotationContext#inspect_nested")

    %{type: {:pi, _, _, {:pi, _, _, {:pi, _, sigma, _}}}} =
      Env.get_def(env, :"SigmaAnnotationContext#inspect_nested")

    assert {:data, _, [{:level_value, _}, {:level_value, _}, _, {:lam, _, _, {:data, _, [tag, machine], []}}], []} =
             sigma

    assert {:app, {:app, {:global, :"SigmaAnnotationContext#tag"}, {:var, 2}}, {:var, 1}} = tag
    assert {:app, {:app, {:global, :"SigmaAnnotationContext#machine"}, {:var, 2}}, {:var, 1}} = machine
  end

  test "Pi, tuple and refinement annotations preserve saturated implicit helper calls" do
    for annotation <- [
          "((destination: Nat) -> Path(tag(compilation), machine(compilation)))",
          "((Nat) -> Path(tag(compilation), machine(compilation)))",
          "Tuple(Nat, Path(tag(compilation), machine(compilation)))",
          "{destination: Nat | predicate(compilation, destination)}"
        ] do
      source = """
      mod AnnotationContextProbe
        type Shape = UnitShape
        type Compilation indices (shape: Shape)
          EmptyCompilation : Compilation(UnitShape)
        @reducible
        fn tag({shape: Shape}, compilation: Compilation(shape)) -> Nat = Z()
        type Machine indices (index: Nat)
          EmptyMachine : Machine(Z())
        @reducible
        fn machine({shape: Shape}, compilation: Compilation(shape)) -> Machine(tag(compilation)) = EmptyMachine()
        type Path(index: Nat, machine: Machine(index)) indices ()
          MkPath : Path(index, machine)
        fn predicate({shape: Shape}, compilation: Compilation(shape), value: Nat) -> Type = Nat
        fn inspect({shape: Shape}, compilation: Compilation(shape), packed: #{annotation}) -> Nat = Z()
      end
      """

      assert {:ok, env} = Program.elaborate(source)
      assert :ok = Kernel.check_def_type(env, :"AnnotationContextProbe#inspect")
      assert :ok = Kernel.check_def(env, :"AnnotationContextProbe#inspect")
    end
  end

  test "the new Sigma binder has its own type rather than the previous binder's type" do
    for annotation <- [
          "Sigma(inner: Compilation(RightShape), At(tag(inner)))",
          "((inner: Compilation(RightShape)) -> At(tag(inner)))"
        ] do
      source = """
      mod SigmaFreshBinderContext
        type Shape = LeftShape | RightShape
        type Compilation indices (shape: Shape)
          LeftCompilation : Compilation(LeftShape)
          RightCompilation : Compilation(RightShape)
        fn tag({shape: Shape}, compilation: Compilation(shape)) -> Nat = match compilation
          LeftCompilation() -> Z()
          RightCompilation() -> S(Z())
        type At indices (index: Nat)
          Here : At(index)
        fn inspect(outer: Compilation(LeftShape), packed: #{annotation}) -> Nat = Z()
      end
      """

      assert {:ok, env} = Program.elaborate(source)
      assert :ok = Kernel.check_def_type(env, :"SigmaFreshBinderContext#inspect")
      assert :ok = Kernel.check_def(env, :"SigmaFreshBinderContext#inspect")
    end
  end

  test "a Sigma domain that is a value is rejected before extending the context" do
    source = """
    mod BadSigmaAnnotationContext
      fn inspect(value: Nat, packed: Sigma(inner: value, Nat)) -> Nat = Z()
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end
end
