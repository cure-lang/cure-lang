defmodule Cure.Diagnostic.VerdictCorpusTest do
  @moduledoc """
  Frozen cross-boundary verdicts.

  This corpus deliberately records only the public-path verdict and its broad
  owner.  It is a regression gate for acceptance drift, not a snapshot of
  diagnostic wording, spans, or implementation error terms.
  """

  use ExUnit.Case, async: false

  alias Antigen.{Challenge, Generators.ElabComplete}
  alias Antigen.Assays.Elab
  alias Cure.Compiler
  alias Cure.Core.{Builtins, Context, Env, Kernel}
  alias Cure.Elab.Program

  @corpus [
    %{id: :parser_accept, domain: :parser, status: :accept, category: :accepted},
    %{id: :parser_reject, domain: :parser, status: :reject, category: :parse_error},
    %{id: :elaboration_accept, domain: :elaboration, status: :accept, category: :accepted},
    %{id: :elaboration_reject, domain: :elaboration, status: :reject, category: :unknown_global},
    %{id: :kernel_accept, domain: :kernel, status: :accept, category: :accepted},
    %{id: :kernel_reject, domain: :kernel, status: :reject, category: :unbound_var},
    %{id: :macro_accept, domain: :macro, status: :accept, category: :accepted},
    %{id: :macro_reject, domain: :macro, status: :reject, category: :codegen_error},
    %{id: :stdlib_accept, domain: :stdlib, status: :accept, category: :accepted},
    %{id: :stdlib_reject, domain: :stdlib, status: :reject, category: :missing_stdlib_source},
    %{id: :antigen_accept, domain: :antigen, status: :accept, category: :accepted},
    %{id: :antigen_reject, domain: :antigen, status: :reject, category: :rejected_well_typed}
  ]

  test "public-path verdicts match the frozen corpus" do
    assert Enum.map(@corpus, &Map.take(&1, [:id, :domain, :status, :category])) ==
             Enum.map(@corpus, fn %{id: id, domain: domain, category: category} ->
               %{id: id, domain: domain, status: verdict(id), category: stable_category(id, category)}
             end)
  end

  defp raw_verdict(:parser_accept), do: Cure.Compiler.parse_source("sup App.Root\n  children []\n")
  defp raw_verdict(:parser_reject), do: Cure.Compiler.parse_source("mod Corpus\n  fn f( = 0\n")

  defp raw_verdict(:elaboration_accept), do: Program.elaborate("mod Corpus\n  fn id(x: Int) -> Int = x\nend\n")
  defp raw_verdict(:elaboration_reject), do: Program.elaborate("mod Corpus\n  fn id() -> Int = missing\nend\n")

  defp raw_verdict(:kernel_accept), do: Kernel.infer(kernel_context(), {:int_lit, 1})
  defp raw_verdict(:kernel_reject), do: Kernel.infer(kernel_context(), {:var, 0})

  defp raw_verdict(:macro_accept), do: Compiler.compile_string(macro_source("0"), emit_events: false)
  defp raw_verdict(:macro_reject), do: Compiler.compile_string(macro_source("missing"), emit_events: false)

  defp raw_verdict(:stdlib_accept), do: Program.elaborate(stdlib_source("Std.List"))
  defp raw_verdict(:stdlib_reject), do: Program.elaborate(stdlib_source("Std.NoSuchModule"))

  defp raw_verdict(:antigen_accept) do
    challenge =
      Challenge.new(
        kind: :elab_program,
        assay: "elab/completeness",
        label: :well_typed,
        payload: %{id: "corpus_accept", src: ElabComplete.source("idx_only/var/rebuild")}
      )

    Elab.run(challenge)
  end

  defp raw_verdict(:antigen_reject) do
    source = "mod P\n  fn f() -> Int = true\nend\n"

    challenge =
      Challenge.new(
        kind: :elab_program,
        assay: "elab/completeness",
        label: :well_typed,
        payload: %{id: "corpus_reject", src: source}
      )

    Elab.run(challenge)
  end

  defp verdict(id), do: status(raw_verdict(id))

  defp status({:ok, _}), do: :accept
  defp status({:ok, _, _}), do: :accept
  defp status(:ok), do: :accept
  defp status({:violation, _}), do: :reject
  defp status({:error, _}), do: :reject

  defp stable_category(id, expected) do
    case raw_verdict(id) do
      result when is_tuple(result) ->
        assert category(result) == expected,
               "stable category drifted for #{id}: expected #{inspect(expected)}, got #{inspect(category(result))}"

        expected

      result ->
        assert category(result) == expected,
               "stable category drifted for #{id}: expected #{inspect(expected)}, got #{inspect(category(result))}"

        expected
    end
  end

  defp category({:ok, _}), do: :accepted
  defp category({:ok, _, _}), do: :accepted
  defp category(:ok), do: :accepted
  defp category({:error, {:source_context, reason, context}}), do: category({:source_context, reason, context})
  defp category({:source_context, reason, _context}), do: category(reason)
  defp category({tag, _first, _second}) when is_atom(tag), do: tag
  defp category({:error, {tag, _}}) when is_atom(tag), do: tag
  defp category({:error, {tag, _, _}}) when is_atom(tag), do: tag
  defp category({:violation, {tag, _}}) when is_atom(tag), do: tag
  defp category({:violation, {tag, _, _}}) when is_atom(tag), do: tag
  defp category({:violation, tag}) when is_atom(tag), do: tag
  defp category(other), do: {:unclassified, other}

  defp kernel_context, do: Context.empty(Builtins.seed(Env.empty()))

  defp macro_source(body),
    do: "mod Corpus\n  macro Value\n    syntax value becomes #{body}\n  fn f() -> Int = value\nend\n"

  defp stdlib_source(module), do: "mod Corpus\n  use #{module}\n  fn id(x: Int) -> Int = x\nend\n"
end
