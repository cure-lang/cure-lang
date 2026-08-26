defmodule Cure.Compiler.CanonicalModulePipelineBeamProductTest do
  @moduledoc """
  A published generation must carry loadable BEAMs, not interfaces alone.

  `Publication.publish/3` installs one `.cifc` per module and an index naming
  them. That is everything a *checker* needs: the next run resolves imports out
  of the generation without touching source. It is not everything a *runner*
  needs. `test/test_helper.exs` loads the stdlib and then `:code.stick_mod/1`s
  every module so no test can accidentally recompile one — and sticking demands
  a resident module, which demands bytecode. There is no interface-to-bytecode
  step, so the canonical pipeline could not replace the legacy sweep even though
  it already checks every module the sweep checks.

  The missing piece is small and entirely determined by what a checked run
  already holds: `body_envs` is the elaborated env per module and `asts` names
  which defs each module owns, which is exactly `Cure.Elab.Emit.compile_forms/3`'s
  input. Emitting is therefore a *product* of a run — the `:products` field the
  request has always carried — rather than a separate compile.

  Publishing them together is the point. A generation whose beams were installed
  by a second, non-atomic pass could be read between the two, and a reader that
  saw interfaces without their beams would conclude the generation was complete.
  One rename must continue to publish everything or nothing.
  """
  use ExUnit.Case, async: true

  @moduletag :tmp_dir

  test "a run asked for beams publishes loadable ones alongside its interfaces", %{tmp_dir: dir} do
    source = write!(dir, "value.cure", "mod Beam.Product\n  fn value() -> Int = 1\n")
    output = Path.join(dir, "output")

    assert {:ok, _checked} =
             check([source], dir,
               output: output,
               generation: 1,
               publication: :atomic,
               products: [:beams]
             )

    assert {:ok, published} = pipeline(:open_published_generation, [output])
    assert pipeline(:generation_complete?, [published])
    refute pipeline(:contains_staging_reference?, [published])

    assert {:ok, binary} = pipeline(:read_published_beam, [published, :"Cure.Beam.Product"])
    assert is_binary(binary)

    # Exactly what test_helper does with the sweep's output.
    assert {:module, :"Cure.Beam.Product"} =
             :code.load_binary(:"Cure.Beam.Product", ~c"published", binary)

    assert :erlang.function_exported(:"Cure.Beam.Product", :value, 0)
  after
    purge(:"Cure.Beam.Product")
  end

  test "a run not asked for beams publishes none", %{tmp_dir: dir} do
    source = write!(dir, "value.cure", "mod Beam.Absent\n  fn value() -> Int = 1\n")
    output = Path.join(dir, "output")

    assert {:ok, _checked} = check([source], dir, output: output, generation: 1, publication: :atomic)

    assert {:ok, published} = pipeline(:open_published_generation, [output])
    assert pipeline(:generation_complete?, [published])

    assert {:error, {:no_published_beam, :"Cure.Beam.Absent"}} =
             pipeline(:read_published_beam, [published, :"Cure.Beam.Absent"])
  end

  test "the generation names every beam it published", %{tmp_dir: dir} do
    a = write!(dir, "a.cure", "mod Beam.Many.A\n  fn a() -> Int = 1\n")
    b = write!(dir, "b.cure", "mod Beam.Many.B\n  use Beam.Many.A\n  fn b() -> Int = a()\n")
    output = Path.join(dir, "output")

    assert {:ok, _checked} =
             check([b, a], dir,
               output: output,
               generation: 1,
               publication: :atomic,
               products: [:beams]
             )

    assert {:ok, published} = pipeline(:open_published_generation, [output])
    assert published.beams == [:"Cure.Beam.Many.A", :"Cure.Beam.Many.B"]

    for module <- published.beams do
      assert {:ok, binary} = pipeline(:read_published_beam, [published, module])
      assert {:module, ^module} = :code.load_binary(module, ~c"published", binary)
    end
  after
    purge(:"Cure.Beam.Many.A")
    purge(:"Cure.Beam.Many.B")
  end

  # Checking and emitting do not accept the same modules. An unfilled obligation
  # is a legitimate thing to CHECK — that is what makes holes usable — and an
  # illegitimate thing to run, so `Emit` refuses it (the #102 firewall). That gap
  # is the only way a run can fail after every module has checked, which makes it
  # the executable statement that publication really is all-or-nothing.
  test "a run whose emission fails publishes no generation at all", %{tmp_dir: dir} do
    source = write!(dir, "hole.cure", "mod Beam.Unfinished\n  fn f() -> Int = ?\n")
    output = Path.join(dir, "output")

    assert {:error, {:beam_emission_failed, "Beam.Unfinished", _reason}} =
             check([source], dir,
               output: output,
               generation: 1,
               publication: :atomic,
               products: [:beams]
             )

    refute File.exists?(Path.join(output, "current"))
    assert {:error, {:no_published_generation, ^output, _}} = pipeline(:open_published_generation, [output])
  end

  test "the same module checks and publishes when beams are not a product", %{tmp_dir: dir} do
    source = write!(dir, "hole.cure", "mod Beam.Unfinished.Checked\n  fn f() -> Int = ?\n")
    output = Path.join(dir, "output")

    assert {:ok, _checked} = check([source], dir, output: output, generation: 1, publication: :atomic)
    assert {:ok, published} = pipeline(:open_published_generation, [output])
    assert published.modules == ["Beam.Unfinished.Checked"]
    assert published.beams == []
  end

  defp check(paths, dir, extra) do
    pipeline(:check, [
      paths,
      Keyword.merge([module_pipeline: :canonical, package: "fixture", source_roots: [dir]], extra)
    ])
  end

  defp pipeline(function, arguments), do: apply(Cure.Compiler.ModulePipeline, function, arguments)

  defp purge(module) do
    :code.purge(module)
    :code.delete(module)
  end

  defp write!(dir, name, source) do
    path = Path.join(dir, name)
    File.write!(path, source)
    path
  end
end
