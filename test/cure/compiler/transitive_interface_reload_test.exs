defmodule Cure.Compiler.TransitiveInterfaceReloadTest do
  use ExUnit.Case, async: true

  @moduletag :tmp_dir

  test "an interface-only dependency brings the interfaces its public types require", %{tmp_dir: dir} do
    base =
      write!(
        dir,
        "base.cure",
        """
        mod Reload.Base
          type Token = Token(Int)
        """
      )

    bridge =
      write!(
        dir,
        "bridge.cure",
        """
        mod Reload.Bridge
          use Reload.Base
          typealias PublicToken = Reload.Base.Token
        """
      )

    consumer =
      write!(
        dir,
        "consumer.cure",
        """
        mod Reload.Consumer
          use Reload.Bridge
          type Box = Box(PublicToken)
          fn keep(value: PublicToken) -> Box = Box(value)
        """
      )

    interfaces = Path.join(dir, "interfaces")

    assert {:ok, published} = check([consumer, bridge, base], dir)
    assert :ok = Cure.Compiler.ModulePipeline.write_interfaces(published, interfaces)

    File.rm!(base)
    File.rm!(bridge)

    assert {:ok, reloaded} =
             check([consumer], dir,
               interface_roots: [interfaces],
               forbid_source_fallback: true,
               forbid_beam_resolution: true,
               fresh_environment: true
             )

    assert :ok = Cure.Compiler.ModulePipeline.kernel_verify_interfaces(reloaded)
  end

  defp check(paths, root, opts \\ []) do
    {:ok, stdlib} =
      Cure.Compiler.Artifacts.open_verified_set(
        kind: :stdlib,
        candidates: Cure.Stdlib.Paths.beam_dirs()
      )

    interface_roots =
      (Keyword.get(opts, :interface_roots, []) ++ [stdlib.artifact_root])
      |> Enum.uniq()

    Cure.Compiler.ModulePipeline.check(
      paths,
      Keyword.merge(
        [
          module_pipeline: :canonical,
          package: "transitive-interface-reload",
          source_roots: [root],
          products: [:beams]
        ],
        Keyword.put(opts, :interface_roots, interface_roots)
      )
    )
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
