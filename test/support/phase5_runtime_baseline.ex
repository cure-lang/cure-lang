defmodule Cure.Test.Phase5RuntimeBaseline do
  @moduledoc """
  Runtime evidence captured from committed HEAD before the universe migration.

  Captures emitted Erlang forms, erased Core (the available pre-backend IR),
  exports/arities, and actual BEAM executions. Normalization is the identity:
  `Emit.compile_forms/3` emits fixed line annotations and no source provenance
  attribute; no computational content, module name, or metadata is stripped.
  Toolchain/source identity is kept separately from the comparable payload.
  """

  alias Cure.Elab.{Emit, Erase, Name}

  @root Path.expand("../fixtures/phase5_universe_runtime", __DIR__)
  @head "722ee355665fdac39b3d954fd95e9ae7f7c4b9bd"
  @functions ~w(id apply_to id_result apply_result imported_result list_empty list_cons list_match
    option_none option_some option_match result_ok result_error result_match pack_sigma project_first
    project_second tuple2 tuple3 tuple4 tuple5 tuple6 tuple7 tuple8 tuple_last equivalent
    erase_equivalent)a

  def root, do: @root

  def capture do
    provider = capture_module("phase5_baseline_imported.cure", [:imported_id], [])

    consumer =
      capture_module("phase5_baseline.cure", @functions, [
        {:id, [44]},
        {:id_result, []},
        {:apply_result, []},
        {:imported_result, []},
        {:list_empty, []},
        {:list_cons, []},
        {:list_match, [[]]},
        {:list_match, [[21, 22]]},
        {:option_none, []},
        {:option_some, []},
        {:option_match, [:none]},
        {:option_match, [{:some, 23}]},
        {:result_ok, []},
        {:result_error, []},
        {:result_match, [{:ok, 24}]},
        {:result_match, [{:error, 25}]},
        {:pack_sigma, []},
        {:project_first, [{16, 17}]},
        {:project_second, [{16, 17}]},
        {:tuple2, []},
        {:tuple3, []},
        {:tuple4, []},
        {:tuple5, []},
        {:tuple6, []},
        {:tuple7, []},
        {:tuple8, []},
        {:tuple_last, [{1, 2, 3, 4, 5, 6, 7, 8}]},
        {:equivalent, [26]},
        {:erase_equivalent, [27]}
      ])

    %{provider: provider, consumer: consumer}
  end

  defp capture_module(file, functions, calls) do
    path = Path.join(@root, file)
    source = File.read!(path)

    {:ok, env} =
      Cure.Compiler.check_source(source, file: path, source_roots: [@root])

    module = String.to_atom("Cure." <> env.module_owner)
    {:ok, forms} = Emit.compile_forms(env, module, functions)
    {:ok, ^module} = Emit.compile_and_load(env, module: module, functions: functions)

    exports = for {:attribute, _, :export, entries} <- forms, entry <- entries, do: entry

    erased =
      Map.new(functions, fn name ->
        {_key, definition} =
          Enum.find(env.defs, fn {key, _} ->
            Name.owner(key) == env.module_owner and Name.base(key) == Atom.to_string(name)
          end)

        {name, Erase.erase(env, definition.body)}
      end)

    results = Enum.map(calls, fn {name, args} -> {name, args, apply(module, name, args)} end)
    %{module: module, forms: forms, exports: exports, erased_core: erased, results: results}
  end

  def bytes(payload), do: :erlang.term_to_binary(payload, [:deterministic])
  def digest(payload), do: :crypto.hash(:sha256, bytes(payload)) |> Base.encode16(case: :lower)

  @doc """
  Computational backend surface used for cross-representation comparison.

  The captured erased Core is retained as diagnostic evidence, not normalized
  away: that pre-backend IR deliberately still contains erased binder domains
  and their universe annotations. Only the emitted forms, ABI and executions
  can be compared literally across the Core representation migration.
  """
  def runtime_payload(payload) do
    Map.new(payload, fn {name, module} -> {name, Map.take(module, [:module, :forms, :exports, :results])} end)
  end

  def read! do
    @root |> Path.join("baseline.etf") |> File.read!() |> :erlang.binary_to_term([:safe])
  end

  def freeze! do
    {@head <> "\n", 0} = System.cmd("git", ["--no-pager", "rev-parse", "HEAD"])
    {"", 0} = System.cmd("git", ["--no-pager", "diff", "--exit-code", "HEAD", "--", "lib", "mix.exs", "mix.lock"])
    {lib_tree, 0} = System.cmd("git", ["--no-pager", "rev-parse", "HEAD:lib"])
    first = capture()
    second = capture()
    true = bytes(first) == bytes(second)
    :ok = assert_mutation_sensitive!(first)
    File.write!(Path.join(@root, "baseline.etf"), bytes(first))

    manifest = %{
      "head" => @head,
      "compiler_lib_git_tree" => String.trim(lib_tree),
      "elixir" => System.version(),
      "otp" => :erlang.system_info(:otp_release) |> List.to_string(),
      "erts" => :erlang.system_info(:version) |> List.to_string(),
      "normalization" => "identity; no forms, annotations, IR nodes, or module names removed",
      "capture_runs" => 2,
      "same_bytes" => true,
      "literal_mutation_detected" => true,
      "arity_mutation_detected" => true,
      "baseline_limitations" => [
        "local function name sigma_first shadows canonical projection helper: too_many_arguments or emitted self-recursion; fixture uses project_first/project_second",
        "explicit argument for implicit proof slot rejects index_mismatch; erased binder invoked through emitted arity",
        "match equivalent(18) / reflexive() -> 19 raises cannot certify open body; not frozen as a supported operation"
      ],
      "payload_sha256" => digest(first),
      "sources" =>
        Map.new(Path.wildcard(Path.join(@root, "*.cure")), fn path ->
          {Path.basename(path), :crypto.hash(:sha256, File.read!(path)) |> Base.encode16(case: :lower)}
        end)
    }

    File.write!(Path.join(@root, "manifest.json"), :json.encode(manifest))
    manifest
  end

  def assert_mutation_sensitive!(payload) do
    literal_forms =
      Enum.map(payload.consumer.forms, fn
        {:function, line, :id_result, 0, clauses} ->
          {:function, line, :id_result, 0, mutate_literal(clauses)}

        form ->
          form
      end)

    arity_forms =
      Enum.map(payload.consumer.forms, fn
        {:function, line, :id, arity, clauses} -> {:function, line, :id, arity + 1, clauses}
        form -> form
      end)

    false = bytes(payload) == bytes(put_in(payload.consumer.forms, literal_forms))
    false = bytes(payload) == bytes(put_in(payload.consumer.forms, arity_forms))
    :ok
  end

  defp mutate_literal({:integer, line, 41}), do: {:integer, line, 4101}

  defp mutate_literal(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.map(&mutate_literal/1) |> List.to_tuple()

  defp mutate_literal(list) when is_list(list), do: Enum.map(list, &mutate_literal/1)
  defp mutate_literal(leaf), do: leaf
end
