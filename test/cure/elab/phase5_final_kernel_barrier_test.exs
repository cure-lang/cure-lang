defmodule Cure.Elab.Phase5FinalKernelBarrierTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.ModuleInterface
  alias Cure.Compiler.ModulePipeline.Interface
  alias Cure.Core.{Env, Kernel, UniverseCodec}
  alias Cure.Elab.{Emit, Program}

  @moduletag :tmp_dir

  @bad_source """
  mod FinalKernelBarrier
    type Bit = Off | On
    fn bad(value: Off()) -> Atom = :ok
  end
  """

  test "an unused constructor value cannot be admitted as a parameter type", %{tmp_dir: dir} do
    assert {:error, :not_a_type} = Program.elaborate(@bad_source)
    assert {:error, :not_a_type} = Cure.Compiler.check_source(@bad_source)

    path = Path.join(dir, "bad_domain.cure")
    File.write!(path, @bad_source)
    assert {:error, :not_a_type} = Program.module_interface("FinalKernelBarrier", path)

    output = Path.join(dir, "emitted")

    assert {:error, {:codegen_error, :not_a_type}} =
             Cure.Compiler.compile_string_with_artifact(@bad_source,
               file: path,
               output_dir: output,
               emit_events: false
             )

    refute File.exists?(Path.join(output, "Cure.FinalKernelBarrier.beam"))
  end

  test "the well-kinded unused parameter neighbor still checks and publishes", %{tmp_dir: dir} do
    source = String.replace(@bad_source, "value: Off()", "value: Atom")
    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def_type(env, :"FinalKernelBarrier#bad")
    assert :ok = Kernel.check_def(env, :"FinalKernelBarrier#bad")
    assert {:ok, _env} = Cure.Compiler.check_source(source)

    path = Path.join(dir, "good_domain.cure")
    File.write!(path, source)
    assert {:ok, interface} = Program.module_interface("FinalKernelBarrier", path)
    assert :ok = Interface.verify(interface)
  end

  test "an extern has its complete signature checked without checking its sentinel body", %{tmp_dir: dir} do
    bad = """
    mod FinalExternBarrier
      type Bit = Off | On
      @extern(:erlang, :is_atom, 1)
      fn external(value: Off()) -> Bool
    end
    """

    assert {:error, :not_a_type} = Program.elaborate(bad)
    assert {:error, :not_a_type} = Cure.Compiler.check_source(bad)
    path = Path.join(dir, "extern.cure")
    File.write!(path, bad)
    assert {:error, :not_a_type} = Program.module_interface("FinalExternBarrier", path)

    good = String.replace(bad, "value: Off()", "value: Atom")
    assert {:ok, env} = Program.elaborate(good)
    assert %{body: {:extern, {:erlang, :is_atom, 1}}} = Env.get_def(env, :"FinalExternBarrier#external")
    assert :ok = Kernel.check_def_type(env, :"FinalExternBarrier#external")
    assert {:ok, _env} = Cure.Compiler.check_source(good)
  end

  test "mutual runtime functions and transparent aliases reach the barrier only after completion" do
    source = """
    mod FinalMutualBarrier
      typealias Carrier = Atom
      fn left(value: Carrier) -> Carrier = right(value)
      fn right(value: Carrier) -> Carrier = left(value)
    end
    """

    assert {:ok, env} = Program.elaborate(source)

    for name <- [:"FinalMutualBarrier#Carrier", :"FinalMutualBarrier#left", :"FinalMutualBarrier#right"] do
      assert :ok = Kernel.check_def(env, name)
    end

    assert {:ok, _env} = Cure.Compiler.check_source(source)
  end

  test "certified type-level computations remain available while full signatures are checked" do
    source = """
    mod FinalTypeLevelBarrier
      type Tag = Left | Right
      fn Carrier(which: Tag) -> Type = match which
        Left() -> Atom
        Right() -> Atom
      fn preserve({which: Tag}, value: Carrier(which)) -> Carrier(which) = value
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, :"FinalTypeLevelBarrier#Carrier")
    assert :ok = Kernel.check_def(env, :"FinalTypeLevelBarrier#preserve")
    assert {:ok, _env} = Cure.Compiler.check_source(source)
  end

  test "development holes are still admitted but cannot cross the emission firewall" do
    source = """
    mod FinalHoleBarrier
      fn missing(value: Atom) -> Atom = ?goal
    end
    """

    assert {:ok, env} = Program.elaborate(source)
    assert {:ok, _env} = Cure.Compiler.check_source(source)
    assert :ok = Kernel.check_def(env, :"FinalHoleBarrier#missing")

    assert {:error, {:unfilled_hole, _details}} =
             Emit.compile_forms(env, :"Cure.FinalHoleBarrier", [:"FinalHoleBarrier#missing"])
  end

  test "signature skeleton preparation is not mistaken for completed definition admission", %{tmp_dir: dir} do
    source = """
    mod FinalHeaderBarrier
      type Carrier = Here | There
      fn left(value: Carrier) -> Carrier = right(value)
      fn right(value: Carrier) -> Carrier = left(value)
    end
    """

    path = Path.join(dir, "headers.cure")
    File.write!(path, source)
    assert {:ok, types} = Program.module_type_skeleton("FinalHeaderBarrier", path)

    assert {:ok, signatures} =
             Program.module_signature_skeleton("FinalHeaderBarrier", path, [{"FinalHeaderBarrier", types}])

    assert %{body: {:hole, "__pending__"}} = Env.get_def(signatures, :"FinalHeaderBarrier#left")
    assert {:ok, _env} = Program.elaborate(source, file: path)
  end

  test "an opaque imported body is not rechecked as an owned source definition", %{tmp_dir: dir} do
    provider = """
    mod FinalOpaqueProvider
      fn identity(value: Atom) -> Atom = value
    end
    """

    path = Path.join(dir, "provider.cure")
    File.write!(path, provider)
    assert {:ok, interface} = Program.module_interface("FinalOpaqueProvider", path)
    assert {:ok, imported} = Interface.to_env(interface)
    assert %{body: {:hole, "__interface_opaque__"}} = Env.get_def(imported, :"FinalOpaqueProvider#identity")

    consumer = """
    mod FinalOpaqueConsumer
      use FinalOpaqueProvider
      fn keep(value: Atom) -> Atom = identity(value)
    end
    """

    assert {:ok, _env} = Program.elaborate(consumer, source_roots: [dir])
  end

  test "a resident generation-five source interface is not reused by the admission policy" do
    path = Path.expand("lib/std/core.cure")
    identity = UniverseCodec.identity()
    old_key = {Program, :module_interface, path, {5, identity}}
    previous = :persistent_term.get(old_key, :absent)
    source_hash = :crypto.hash(:sha256, File.read!(path))

    poison =
      ModuleInterface.new(%{
        module_name: "PreBarrierPoison",
        source_path: path,
        source_hash: source_hash
      })

    :persistent_term.put(old_key, {:cached, source_hash, {:ok, poison}})

    on_exit(fn ->
      if previous == :absent,
        do: :persistent_term.erase(old_key),
        else: :persistent_term.put(old_key, previous)
    end)

    refute Program.module_interface_cache_identity() == {5, identity}
    assert {:ok, interface} = Program.module_interface("Std.Core", path)
    assert interface.module_name == "Std.Core"
    assert :ok = ModuleInterface.validate(interface)
    assert :persistent_term.get(old_key) == {:cached, source_hash, {:ok, poison}}
  end
end
