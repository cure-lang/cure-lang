defmodule Cure.Compiler.ModuleInterfaceHashTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.ModuleInterface
  alias Cure.Elab.Program

  test "a real stdlib export_env is serializable and hashes deterministically" do
    {:ok, iface} = Program.module_interface("Std.Core", "lib/std/core.cure")
    h1 = iface.interface_hash
    h2 = iface.interface_hash
    assert is_binary(h1) and byte_size(h1) == 32
    assert h1 == h2
  end

  test "different envs hash differently" do
    {:ok, core} = Program.module_interface("Std.Core", "lib/std/core.cure")
    {:ok, list} = Program.module_interface("Std.List", "lib/std/list.cure")
    assert ModuleInterface.semantic_hash(core) != ModuleInterface.semantic_hash(list)
  end
end
