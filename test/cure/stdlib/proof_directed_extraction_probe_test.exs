defmodule Cure.Stdlib.ProofDirectedExtractionProbeTest do
  use ExUnit.Case, async: false
  use ExUnitProperties

  @module :"Cure.Std.ProofDirectedExtraction"

  test "accepted data is extracted totally from erased shape evidence" do
    assert apply(@module, :accepted_number_example, []) == {:AcceptedNumber, 42}
    assert apply(@module, :accepted_flag_example, []) == {:AcceptedFlag, true}
    assert apply(@module, :extract_number_example, []) == 42
    assert apply(@module, :extract_flag_example, []) == true
    assert apply(@module, :contextual_remainder_example, []) == [?b]
  end

  test "the accepted-data consumer is certified total" do
    source = File.read!("lib/std/proof_directed_extraction.cure")
    assert {:ok, env} = Cure.Elab.Program.elaborate(source)
    assert Cure.Core.Env.certified?(env, :"Std.ProofDirectedExtraction#extract")
  end

  property "generated accepted values cross the erased proof and shape-index boundary" do
    check all(
            number <- integer(-10_000..10_000),
            flag <- boolean(),
            max_runs: 50
          ) do
      assert apply(@module, :extract, [{:AcceptedNumber, number}]) == number
      assert apply(@module, :extract, [{:AcceptedFlag, flag}]) == flag
    end
  end

  test "the accepted package and total consumer contain no runtime evidence" do
    {:ok, set} =
      Cure.Compiler.Artifacts.open_verified_set(
        kind: :stdlib,
        candidates: Cure.Stdlib.Paths.beam_dirs()
      )

    artifact =
      set.modules["Std.ProofDirectedExtraction"].artifacts
      |> Enum.find(&(&1.module == Atom.to_string(@module)))

    beam = File.read!(Path.join(set.artifact_root, artifact.path))
    {:beam_file, @module, _exports, _attrs, _info, functions} = :beam_disasm.file(beam)

    runtime_code =
      for {:function, name, _arity, _label, instructions} <- functions,
          name in [
            :accepted_number_example,
            :accepted_flag_example,
            :contextual_example,
            :contextual_remainder_example,
            :extract,
            :remainder
          ],
          do: instructions

    binary = :erlang.term_to_binary(runtime_code)
    refute binary =~ "NumberEvidence"
    refute binary =~ "FlagEvidence"
    refute binary =~ "Consumed"
    refute binary =~ "Same"
    refute binary =~ "Drop"
  end
end
