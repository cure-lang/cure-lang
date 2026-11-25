defmodule Cure.Elab.Phase5ColdInterfaceTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.ModuleInterface
  alias Cure.Compiler.ModulePipeline.Interface
  alias Cure.Core.{Context, Conv, Env, Kernel, Sort}
  alias Cure.Elab.Program

  @moduletag :tmp_dir
  @owner "ColdAliasProvider"
  @a :"ColdAliasProvider#A"
  @b :"ColdAliasProvider#B"

  defp cold_interface(dir) do
    source = """
    mod ColdAliasProvider
      typealias A = Atom
      typealias B = Atom
      fn identity(x: A) -> B = x
    end
    """

    path = Path.join(dir, "cold_alias_provider.cure")
    File.write!(path, source)
    assert {:ok, interface} = Program.module_interface(@owner, path)
    {interface, source, path}
  end

  test "cold source uses the canonical checked certificate projection", %{tmp_dir: dir} do
    {interface, source, path} = cold_interface(dir)
    assert is_nil(interface.owned_env)
    assert is_nil(interface.export_env)
    assert interface.source_hash == :crypto.hash(:sha256, source)
    assert :ok = ModuleInterface.validate(interface)
    assert {:ok, restored} = Interface.to_env(interface)
    assert MapSet.member?(restored.certified, @a)
    assert MapSet.member?(restored.certified, @b)
    assert Conv.conv?({:global, @a}, {:global, @b}, [], 0, restored)
    assert :ok = Kernel.check_def_type(restored, :"ColdAliasProvider#identity")

    assert {:ok, checked} = Program.elaborate(source, file: path)
    payload = Interface.canonical_payload(checked, @owner)
    assert interface.canonical_declarations == payload.canonical_declarations
    assert interface.canonical_externs == payload.canonical_externs
  end

  test "serialized interface round trips preserve certified alias equality", %{tmp_dir: dir} do
    {interface, _source, _path} = cold_interface(dir)
    output = Path.join(dir, "interfaces")
    assert :ok = Interface.write(interface, output)
    assert {:ok, reread} = Interface.read(Interface.path(output, @owner))
    assert reread.interface_hash == interface.interface_hash
    assert reread.canonical_declarations == interface.canonical_declarations
    assert {:ok, restored} = Interface.to_env(reread)
    assert Conv.conv?({:global, @a}, {:global, @b}, [], 0, restored)

    tampered = put_in(reread.canonical_declarations.delta_certified, MapSet.new())
    assert {:error, {:module_interface_hash_mismatch, @owner, _}} = Interface.to_env(tampered)

    assert {:error, {:module_interface_schema_incompatible, _, _}} =
             Interface.to_env(%{reread | schema_version: ModuleInterface.schema_version() - 1})
  end

  test "body availability and forged compatibility environments do not grant unfolding" do
    owner = "UncertifiedAlias"
    name = :"UncertifiedAlias#A"

    env =
      Env.empty()
      |> Env.with_owner(owner)
      |> Env.add_def(:A, {:type, Sort.finite_zero()}, {:atom_type})
      |> then(fn env ->
        update_in(env.defs[name], &Map.merge(&1, %{typealias: true, reducible: true}))
      end)

    interface =
      env
      |> Interface.canonical_payload(owner)
      |> Map.merge(%{
        module_name: owner,
        source_path: "uncertified_alias.cure",
        source_hash: :crypto.hash(:sha256, "uncertified alias")
      })
      |> ModuleInterface.new()

    assert {:ok, restored} = Interface.to_env(interface)
    assert Env.get_def(restored, name).body == {:atom_type}
    refute MapSet.member?(restored.certified, name)
    refute Conv.conv?({:global, name}, {:atom_type}, [], 0, restored)

    # Deliberately forge only the unauthenticated legacy compatibility fields.
    forged = Env.certify(env, name)
    forged_interface = %{interface | owned_env: forged, export_env: forged}
    assert :ok = ModuleInterface.validate(forged_interface)
    assert {:ok, restored} = Interface.to_env(forged_interface)
    refute MapSet.member?(restored.certified, name)
    refute Conv.conv?({:global, name}, {:atom_type}, [], 0, restored)
    assert {:ok, _type} = Kernel.infer(Context.empty(restored), {:global, name})
  end

  test "cold imported aliases agree in a handwritten method signature" do
    source = """
    mod ColdBeamAliasConsumer
      use Std.Beam
      type Message = Ping | Data(Int)
      implementation BeamEncode for Message
        fn to_beam(message: Message) -> BeamTerm = forget(:wire_message)
      fn encode(message: Message) -> BeamTerm = to_beam(message)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)

    wrong = String.replace(source, "-> BeamTerm = forget(:wire_message)", "-> Int = 0")
    assert {:error, reason} = Program.elaborate(wrong)
    assert {:method_signature_mismatch, %{method: :to_beam}} = Program.semantic_error(reason)
  end
end
