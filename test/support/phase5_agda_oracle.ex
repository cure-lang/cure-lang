defmodule Cure.Test.Phase5AgdaOracle do
  @moduledoc """
  Explicit live Agda-side universe gate, independent of Cure's implementation.

  Run from a repository checkout with:

      elixir -r test/support/phase5_agda_oracle.ex \
        -e 'Cure.Test.Phase5AgdaOracle.verify!()'

  Requires Agda 2.8 or newer. Missing tools/imports, syntax failures, unsolved
  metas, incomplete matches, and unexpected diagnostics are errors, never
  successful negative cases. Fixtures are copied under this checkout's `_build`
  before execution; source fixtures and shared caches are not output directories.
  Recorded verdicts are Agda-side only until paired Cure judgments are executed.
  """

  @project Path.expand("../..", __DIR__)
  @fixtures Path.join(@project, "test/fixtures/phase5_universe_oracle")
  @scratch Path.join(@project, "_build/phase5-universe-oracle")
  @flags ~w(--no-level-universe --no-type-in-type --no-omega-in-omega --cumulativity
    --no-allow-unsolved-metas --no-allow-incomplete-matches --warning=error)

  @cases [
    {"LevelSmall", "UniverseLevel : Type0 under --no-level-universe", :accept},
    {"Formation", "Type(a) : Type(succ(a)); Type37 : Type38; polymorphic identity", :accept},
    {"Cumulativity", "A : Type(a) lifts to Type(max(a,b)); literal Type(a) requires max(succ(a),b)", :accept},
    {"MaximumLaws", "definitional maximum-plus laws proved by the equality constructor", :accept},
    {"PiSorts", "independent Pi has finite join; rigid level-dependent Pi has TypeLimit0; limit hierarchy", :accept},
    {"RejectSelf", "Type(a) does not inhabit Type(a)",
     {:reject, "Set (Agda.Primitive.lsuc a) is not less or equal than Set a"}},
    {"RejectDescending", "a+1 is not below a", {:reject, "Set (lsuc a) is not less or equal than Set a"}},
    {"RejectUnrelated", "unrelated open levels do not compare", {:reject, "Set a is not less or equal than Set b"}},
    {"RejectLimitSelf", "TypeLimit0 does not inhabit itself", {:reject, "Setω₁ is not less or equal than Setω"}},
    {"RejectLimitFinite", "limit sorts never fit below finite sorts",
     {:reject, "Setω₁ is not less or equal than Set a"}},
    {"RejectDependentFinite", "rigidly level-dependent Pi has no finite sort",
     {:reject, "Agda.Primitive.Setω is not less or equal than Set a"}},
    {"RejectLiteralLift", "literal Type(a) cannot use the inhabitant-lift shorthand",
     {:reject, "Set (Agda.Primitive.lsuc a) is not less or equal than Set (a ⊔ b)"}}
  ]

  @doc "Execute every fixture and write measured evidence under worktree-local `_build`."
  def verify! do
    agda = System.find_executable("agda") || raise "Phase 5 oracle requires an actual Agda executable"
    {version, 0} = System.cmd(agda, ["--version"], stderr_to_stdout: true)
    require_version!(version)
    {agda_dir, 0} = System.cmd(agda, ["--print-agda-dir"], stderr_to_stdout: true)
    primitive = Path.join(String.trim(agda_dir), "lib/prim/Agda/Primitive.agda")
    primitive_hash = hash(File.read!(primitive))

    File.mkdir_p!(@scratch)
    run = Path.join(@scratch, "run-#{System.pid()}-#{System.unique_integer([:positive, :monotonic])}")
    File.mkdir!(run)
    tmp = Path.join(run, "tmp")
    File.mkdir!(tmp)

    results =
      Enum.map(@cases, fn {name, contract, expectation} ->
        file = name <> ".agda"
        source = File.read!(Path.join(@fixtures, file))
        require_safe_fixture!(source, file)
        copy = Path.join(run, file)
        File.write!(copy, source)

        {output, status} =
          System.cmd(agda, @flags ++ ["-i", run, copy],
            cd: run,
            env: [{"TMPDIR", tmp}],
            stderr_to_stdout: true
          )

        check_verdict!(file, expectation, output, status)

        %{
          "fixture" => file,
          "source_sha256" => hash(source),
          "contract" => contract,
          "expected" => if(expectation == :accept, do: "accept", else: "reject"),
          "actual_exit_status" => status,
          "verified_diagnostic" => diagnostic(expectation),
          "output" => String.replace(output, run, "<oracle-workspace>")
        }
      end)

    evidence = %{
      "stage" => "agda_side_only",
      "cure_pair_status" => "pending_actual_kernel_and_source_judgments",
      "agda_version" => String.trim(version),
      "agda_primitive_source_sha256" => primitive_hash,
      "flags" => @flags,
      "normalization" => "replace only temporary fixture workspace paths in diagnostic output",
      "fixtures" => results
    }

    File.write!(Path.join(@scratch, "evidence.json"), :json.encode(evidence))
    IO.puts("Phase 5 Agda-side oracle: 5 accepted, 7 designated universe rejections verified")
    evidence
  end

  defp require_version!(version) do
    case Regex.run(~r/Agda version (\d+)\.(\d+)/, version) do
      [_, major, minor] ->
        unless String.to_integer(major) > 2 or
                 (String.to_integer(major) == 2 and String.to_integer(minor) >= 8) do
          raise "Phase 5 oracle requires Agda >= 2.8, got #{String.trim(version)}"
        end

      _ ->
        raise "Cannot identify actual Agda version: #{inspect(version)}"
    end
  end

  defp require_safe_fixture!(source, file) do
    forbidden = ~r/\bpostulate\b|\{-#|\{!!\}|\?/

    if Regex.match?(forbidden, source) do
      raise "#{file}: fixture may not add postulates, pragmas, holes, or unsafe declarations"
    end

    imports = Regex.scan(~r/\bimport\s+([A-Za-z][A-Za-z0-9_.]*)/, source, capture: :all_but_first)
    unless imports == [["Agda.Primitive"]], do: raise("#{file}: unexpected fixture imports")
  end

  defp check_verdict!(_file, :accept, _output, 0), do: :ok

  defp check_verdict!(file, {:reject, relation}, output, status) when status != 0 do
    error_codes = Regex.scan(~r/\berror: \[([A-Za-z0-9]+)\]/, output, capture: :all_but_first)
    error_count = ~r/\berror:/ |> Regex.scan(output) |> Enum.count()

    unless error_codes == [["NotLeqSort"]] and error_count == 1 and
             not String.contains?(output, "warning:") and String.contains?(output, relation) do
      raise "#{file}: failed for an unexpected reason, not designated universe rejection:\n#{output}"
    end
  end

  defp check_verdict!(file, expectation, output, status) do
    raise "#{file}: expected #{inspect(expectation)}, got exit #{status}:\n#{output}"
  end

  defp diagnostic(:accept), do: nil
  defp diagnostic({:reject, relation}), do: %{"code" => "NotLeqSort", "relation" => relation}
  defp hash(bytes), do: :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)
end
