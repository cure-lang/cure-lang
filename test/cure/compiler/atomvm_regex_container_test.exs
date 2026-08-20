defmodule Cure.Compiler.AtomVMRegexContainerTest do
  use ExUnit.Case, async: false

  @moduletag :atomvm
  @moduletag timeout: 240_000

  alias Cure.Compiler.{Artifacts, PortableClosure}

  test "the portable Std.Regex closure runs unchanged in generic-unix AtomVM" do
    atomvm_root = System.get_env("ATOMVM_ROOT", "/Users/ch/Develop/esp32-beam/AtomVM")
    atomvm = Path.join(atomvm_root, "build/src/AtomVM")
    packbeam = Path.join(atomvm_root, "build/tools/packbeam/packbeam")
    estdlib = Path.join(atomvm_root, "build/libs/estdlib/src/beams")

    if File.exists?(atomvm) and File.exists?(packbeam) and File.dir?(estdlib) do
      out = Path.join(System.tmp_dir!(), "cure_regex_atomvm_#{System.unique_integer([:positive])}")
      File.mkdir_p!(out)
      on_exit(fn -> File.rm_rf!(out) end)

      source = """
      mod RegexAtomVMProbe
        use Std.Regex
        fn check() -> Bool = matches(/a/, "za")
      end
      """

      assert {:ok, module, []} =
               Cure.Compiler.compile_string(source, output_dir: out, emit_events: false)

      assert module == :"Cure.RegexAtomVMProbe"
      probe = Path.join(out, "Cure.RegexAtomVMProbe.beam")
      assert File.regular?(probe)

      stdlib_root =
        File.cwd!()
        |> Path.join("_build/cure/ebin")
        |> Cure.Compiler.Artifacts.Writer.resolve()

      assert {:ok, report} = PortableClosure.audit("_build/cure/ebin", package: "cure_regex")
      assert report.forbidden == []

      assert {:module, ^module} = :code.load_abs(String.to_charlist(Path.rootname(probe)))
      assert apply(module, :check, []) == true

      assert {:ok, set} = Artifacts.open_verified_set("_build/cure/ebin", verification: :full)

      closure_original_beams =
        Enum.map(report.modules, fn source_module ->
          set.modules[source_module].artifacts
          |> hd()
          |> Map.fetch!(:path)
          |> then(&Path.join(stdlib_root, &1))
        end)

      closure_beams =
        Enum.zip(report.modules, closure_original_beams)
        |> Enum.map(fn {source_module, path} -> stage_atomvm_beam(path, "Cure." <> source_module, out) end)

      staged_probe = stage_atomvm_beam(probe, "Cure.RegexAtomVMProbe", out)
      char_bridge = :code.which(:cure_std_char) |> List.to_string()
      assert File.regular?(char_bridge)
      staged_char_bridge = stage_atomvm_beam(char_bridge, "cure_std_char", out)
      unicode_beams = Path.wildcard(Path.expand("../../unicode/ebin/*.beam", Path.dirname(char_bridge)))

      forms = [
        {:attribute, 1, :module, :cure_regex_atomvm_probe},
        {:attribute, 1, :export, [{:start, 0}]},
        {:function, 1, :start, 0,
         [
           {:clause, 1, [], [],
            [
              remote_call(
                :io,
                :format,
                [
                  {:string, 1, ~c"CURE_REGEX_ATOMVM=~p~n"},
                  {:cons, 1, remote_call(module, :check, []), {nil, 1}}
                ]
              )
            ]}
         ]}
      ]

      assert {:ok, :cure_regex_atomvm_probe, binary, []} =
               Cure.Compiler.BeamWriter.compile_forms(forms)

      probe_wrapper = Path.join(out, "cure_regex_atomvm_probe.beam")
      File.write!(probe_wrapper, binary)

      archive = Path.join(out, "cure_regex_atomvm.avm")
      beams =
        [probe_wrapper | Path.wildcard(Path.join(estdlib, "*.beam"))] ++
          [staged_probe, staged_char_bridge | closure_original_beams ++ closure_beams ++ unicode_beams]
      {_pack_output, 0} = System.cmd(packbeam, ["create", "--start", "cure_regex_atomvm_probe", archive | Enum.uniq(beams)], cd: atomvm_root)

      {output, 0} = System.cmd(atomvm, [archive], cd: atomvm_root)
      assert output =~ "CURE_REGEX_ATOMVM=true"
    else
      assert true
    end
  end

  defp remote_call(module, function, args) do
    {:call, 1, {:remote, 1, {:atom, 1, module}, {:atom, 1, function}}, args}
  end

  defp stage_atomvm_beam(path, module_name, out) do
    target_name =
      module_name
      |> String.downcase()
      |> String.replace(".", "_")
      |> then(&(&1 <> ".beam"))
    target = Path.join(out, target_name)
    File.cp!(path, target)
    target
  end
end
