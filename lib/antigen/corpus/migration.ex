defmodule Antigen.Corpus.Migration do
  @moduledoc """
  Offline historical import, semantic rekey, and individually reviewed dispositions.

  Audit is read-only. Staging archives complete preimages and writes a per-row
  inventory even when replay fails. Publication is a separate explicit operation;
  it uses input-hash compare-and-swap and a recoverable per-file journal, not a
  claim of atomic multi-file replacement.
  """
  alias Antigen.{Challenge, Corpus, Runner}
  alias Antigen.Corpus.LegacyImport
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Context, Conv, Eval, Kernel, Normalise}

  @corpus_preimage "8c0de74386459e74081c3ec6a3b4df5d9d7f5e9907d23ff86409f9ef951c7479"
  @seeds_preimage "79ea214694d03327299837c778a88c572ce75ce767031e3fccc1c7cfb7edfaca"
  @ceilings %{
    "5d1175173106dc36d49acdd0a51eebb68da1e2869bec06e55905520ce6cb35f2" => "def_ceiling",
    "d082258c2531d7e61c65a1cad68863c93bdc5578100bb5777906265301682023" => "family_ceiling"
  }
  @bad_claims ~w(
    607527a164639b3f45aadd3b4c3dbc6938d854601ae47e7db11ce3207d0a518a
    da42ab2c7696f9b7df4aacc017d13cba436bcc3b6e0ecf17d2df48c481aa8393
    70dcdda655f7380419bcb1e7e09ebb41f4cd0523d40c33e1bdc4279a1fbba00d
    dcaae5226c7188fce9d49aa3908f58eb5a667052fb9dd893a0a0ddddb36cf8a5
    473b3c02c67e52197042c6aec877b046f38d3463192779e4a9f24af518493e40
  )

  @doc "Audit without writing; return the inventory and staged in-memory state."
  def audit(paths, opts \\ []) do
    unless opts[:from] == :fixed_ceiling_v1, do: raise(ArgumentError, "explicit historical era required")
    paths = Enum.map(paths, &Path.expand/1)
    validate_paths!(paths, opts)
    inputs = Enum.map(paths, &input/1)
    inactive = inactive_paths(paths) |> Enum.map(&input/1)
    rows = Enum.flat_map(inputs, &import_file(&1, opts))
    outputs = Enum.flat_map(rows, & &1.outputs)
    {additions, added_outputs} = reviewed_additions(inputs, outputs)
    outputs = outputs ++ added_outputs
    names = MapSet.new(inputs, & &1.name)
    missing = outputs |> Enum.map(& &1.target) |> Enum.reject(&MapSet.member?(names, &1)) |> Enum.uniq()
    failures = for row <- rows, row.error, do: %{"source" => row.source, "line" => row.line, "error" => row.error}
    failures = failures ++ Enum.map(missing, &%{"error" => "missing output store", "store" => &1})
    replay_failures = for output <- outputs, output.replay != "ok", do: output_summary(output)
    before_mutants = rows |> Enum.map(& &1.original) |> Enum.reject(&is_nil/1) |> mutant_inventory()
    after_mutants = outputs |> Enum.map(& &1.challenge) |> Enum.reject(&is_nil/1) |> mutant_inventory()

    failures =
      if before_mutants == after_mutants, do: failures, else: failures ++ [%{"error" => "mutant conservation failed"}]

    inventory = %{
      "format" => "antigen-offline-migration/1",
      "universe" => Corpus.universe_epoch(),
      "antibody_version" => Corpus.antibody_version(),
      "complete" => failures == [] and replay_failures == [],
      "files" =>
        Enum.map(inputs, fn file ->
          out = Enum.filter(outputs, &(&1.target == file.name))

          %{
            "source" => file.path,
            "name" => file.name,
            "sha256" => file.sha,
            "bytes" => byte_size(file.bytes),
            "physical_lines" => length(file.lines),
            "output_records" => length(out),
            "output_sha256" => sha(render(out))
          }
        end),
      "rows" => Enum.map(rows, &row_summary/1),
      "additions" => additions,
      "recipe_review" => recipe_review(),
      "inactive_preimages" =>
        Enum.map(inactive, &%{"name" => &1.name, "sha256" => &1.sha, "bytes" => byte_size(&1.bytes)}),
      "failures" => failures,
      "replay_failures" => replay_failures,
      "mutants_before" => before_mutants,
      "mutants_after" => after_mutants,
      "collisions" => collisions(outputs)
    }

    state = %{inputs: inputs, inactive: inactive, outputs: outputs}
    if inventory["complete"], do: {:ok, inventory, state}, else: {:error, inventory, state}
  end

  defp path_exists?(path) do
    case File.lstat(path) do
      {:ok, _} -> true
      {:error, :enoent} -> false
      {:error, reason} -> raise(File.Error, reason: reason, action: "lstat", path: path)
    end
  end

  @doc "Archive/stage an audited result; unresolved replay always remains an error."
  def stage(paths, opts) do
    archive = opts |> Keyword.fetch!(:archive_dir) |> Path.expand()
    out = opts |> Keyword.fetch!(:out_dir) |> Path.expand()
    inventory_path = opts |> Keyword.fetch!(:inventory) |> Path.expand()
    {status, inventory, state} = audit(paths, opts)
    File.mkdir_p!(archive)
    File.mkdir_p!(out)

    Enum.each(state.inputs ++ state.inactive, fn file ->
      preserve!(Path.join(archive, file.name), file.bytes)
      unless sha(File.read!(Path.join(archive, file.name))) == file.sha, do: raise("archive verification failed")
    end)

    Enum.each(state.inputs, fn file ->
      records = Enum.filter(state.outputs, &(&1.target == file.name))
      preserve!(Path.join(out, file.name), render(records))
    end)

    write_json!(inventory_path, inventory)

    if Keyword.get(opts, :write, false) do
      unless status == :ok, do: raise("migration unresolved; staged evidence retained, publication refused")
      publish!(state, inventory, opts)
    end

    {status, inventory, state}
  end

  @doc """
  Publish a complete staged result, retaining archives and a per-file recovery journal.
  An optional trusted `:on_checkpoint` observer receives each durable published
  entry; it cannot override verification or authorize different bytes.
  """
  def publish!(state, inventory, opts) do
    unless inventory["complete"], do: raise("cannot publish incomplete migration")
    validate_paths!(Enum.map(state.inputs, & &1.path), opts)
    archive = Path.expand(Keyword.fetch!(opts, :archive_dir))
    out = Path.expand(Keyword.fetch!(opts, :out_dir))
    journal_path = Path.expand(Keyword.fetch!(opts, :inventory)) <> ".publish.json"
    if path_exists?(journal_path), do: raise("publication journal already exists; inspect/recover it before retrying")

    Enum.each(state.inactive, fn file ->
      unless sha(File.read!(file.path)) == file.sha and sha(File.read!(Path.join(archive, file.name))) == file.sha,
        do: raise("inactive preimage compare-and-swap preflight failed")
    end)

    entries =
      Enum.map(state.inputs, fn file ->
        output = Path.join(out, file.name)
        archive_path = Path.join(archive, file.name)
        expected = Enum.find(inventory["files"], &(&1["name"] == file.name))

        unless sha(File.read!(file.path)) == file.sha and sha(File.read!(archive_path)) == file.sha and
                 sha(File.read!(output)) == expected["output_sha256"],
               do: raise("publication compare-and-swap preflight failed")

        unless canonical(file.path) == file.path, do: raise("publication through a symlink is not supported")

        %{
          "source" => file.path,
          "archive" => archive_path,
          "staged" => output,
          "input_sha256" => file.sha,
          "output_sha256" => expected["output_sha256"],
          "status" => "prepared",
          "temporary" => file.path <> ".antigen-migration"
        }
      end)

    if Enum.any?(entries, &path_exists?(&1["temporary"])), do: raise("publication temporary already exists")
    journal = %{"format" => "antigen-publication/1", "status" => "prepared", "files" => entries}
    write_json!(journal_path, journal)

    Enum.reduce(Enum.with_index(entries), journal, fn {entry, index}, journal ->
      unless sha(File.read!(entry["source"])) == entry["input_sha256"],
        do: raise("publication source changed; recovery journal retained")

      bytes = File.read!(entry["staged"])
      unless sha(bytes) == entry["output_sha256"], do: raise("staged output changed before publication copy")
      File.write!(entry["temporary"], bytes, [:exclusive, :sync])
      File.chmod!(entry["temporary"], File.stat!(entry["source"]).mode)
      journal = update_entry(journal, index, "replacing")
      write_json!(journal_path, journal)

      unless sha(File.read!(entry["source"])) == entry["input_sha256"],
        do: raise("publication source changed before rename")

      unless sha(File.read!(entry["temporary"])) == entry["output_sha256"],
        do: raise("publication temporary output changed before rename")

      File.rename!(entry["temporary"], entry["source"])
      journal = update_entry(journal, index, "published")
      write_json!(journal_path, journal)
      if observer = opts[:on_checkpoint], do: observer.(Enum.at(journal["files"], index))
      journal
    end)
    |> Map.put("status", "published")
    |> then(&write_json!(journal_path, &1))

    :ok
  end

  defp update_entry(journal, index, status),
    do: Map.update!(journal, "files", &List.update_at(&1, index, fn entry -> Map.put(entry, "status", status) end))

  defp inactive_paths(paths) do
    if Enum.any?(paths, &(Path.basename(&1) == "corpus.sexp")) do
      paths
      |> Enum.map(&Path.dirname/1)
      |> Enum.uniq()
      |> Enum.map(&Path.join(&1, "retired.sexp"))
      |> Enum.filter(&File.regular?/1)
    else
      []
    end
  end

  defp input(path) do
    bytes = File.read!(path)
    lines = String.split(bytes, "\n")
    lines = if String.ends_with?(bytes, "\n"), do: Enum.drop(lines, -1), else: lines
    lines = if bytes == "", do: [], else: lines
    %{path: path, name: Path.basename(path), bytes: bytes, sha: sha(bytes), lines: lines}
  end

  defp import_file(file, opts) do
    file.lines
    |> Enum.with_index(1)
    |> Enum.map(fn {line, index} ->
      base = %{
        source: file.name,
        line: index,
        sha: sha(line),
        original: nil,
        fields: %{},
        actions: [],
        outputs: [],
        error: nil,
        disposition: "preserved"
      }

      if line == "" do
        %{
          base
          | outputs: [%{target: file.name, record: "", challenge: nil, replay: "ok", key: nil}],
            disposition: "blank_line"
        }
      else
        import_row(file, line, base, opts)
      end
    end)
  end

  defp import_row(file, line, base, opts) do
    if file.name == "corpus.sexp" and file.sha == @corpus_preimage and Map.has_key?(@ceilings, base.sha) do
      fields =
        line
        |> String.split("\t")
        |> tl()
        |> Map.new(fn field ->
          field |> String.split("=", parts: 2) |> List.to_tuple()
        end)

      %{
        base
        | disposition: "retired_obsolete_ceiling",
          fields: fields,
          actions: [
            %{
              "action" => "reviewed_ceiling_retirement",
              "id" => Map.fetch!(@ceilings, base.sha),
              "reference" => "../universe_ceiling_retirements.json",
              "authorization_file_sha256" => file.sha
            }
          ]
      }
    else
      import_active_row(file, line, base, opts)
    end
  end

  defp import_active_row(file, line, base, opts) do
    case LegacyImport.decode_record(line, opts) do
      {:ok, item} ->
        base = %{base | original: item.challenge, fields: item.fields, actions: item.actions}

        cond do
          file.name == "seeds.sexp" and file.sha == @seeds_preimage and base.sha in @bad_claims ->
            {negative, positive, checks} = inference_controls(item.challenge)

            %{
              base
              | disposition: "archived_obsolete_positive_claim",
                actions:
                  item.actions ++
                    [
                      %{
                        "action" => "separate_inference_negative_and_checked_positive",
                        "checks" => checks,
                        "original_claim_archived" => true
                      }
                    ],
                outputs: [output(positive, file.name), output(negative, "corpus.sexp")]
            }

          true ->
            %{base | outputs: [output(item.challenge, file.name)]}
        end

      {:error, reason} ->
        %{base | error: inspect(reason, limit: :infinity)}
    end
  rescue
    exception -> %{base | error: Exception.format(:error, exception, __STACKTRACE__)}
  catch
    kind, reason -> %{base | error: inspect({kind, reason}, limit: :infinity)}
  end

  defp output(challenge, target) do
    mode = if target == "seeds.sexp", do: :seed, else: :antibody
    key = Corpus.dedup_key(challenge, mode)
    record = Corpus.encode_record(challenge, key)
    {:ok, decoded} = Corpus.decode_record(record)

    unless Corpus.semantic_descriptor(decoded) == Corpus.semantic_descriptor(challenge),
      do: raise("current output reconstruction changed semantic identity")

    replay =
      try do
        case Runner.replay_one(decoded) do
          :ok -> "ok"
          verdict -> inspect(verdict, limit: :infinity)
        end
      rescue
        exception -> Exception.format(:error, exception, __STACKTRACE__)
      catch
        kind, reason -> inspect({kind, reason}, limit: :infinity)
      end

    %{target: target, record: record, challenge: challenge, key: key, replay: replay}
  end

  defp reviewed_additions(inputs, outputs) do
    if Enum.any?(inputs, &(&1.name == "corpus.sexp" and &1.sha == @corpus_preimage)) do
      generator = Antigen.Generators.Totality
      challenge = generator.diverging_pending_sibling()
      key = Corpus.dedup_key(challenge, :antibody)

      if Enum.any?(outputs, &(&1.target == "corpus.sexp" and &1.key == key)) do
        {[], []}
      else
        :ok = Antigen.Assays.Totality.run(challenge)

        if key == Corpus.dedup_key(generator.diverging_mutual_pair(), :antibody),
          do: raise("pending-sibling semantic antibody collided with full mutual-pair target")

        addition = output(challenge, "corpus.sexp")
        unless addition.replay == "ok", do: raise("pending-sibling replay failed")
        fresh_replay!(addition.record)
        source = generator.module_info(:compile) |> Keyword.fetch!(:source) |> List.to_string()

        provenance = %{
          "reason" =>
            "Separately reviewed required pending-sibling guard; old piece-only identity collided with full mutual pair despite distinct pending/focus setup.",
          "generator" => "Antigen.Generators.Totality.diverging_pending_sibling/0",
          "source" => "lib/antigen/generators/totality.ex",
          "source_sha256" => source |> File.read!() |> sha(),
          "fresh_replay" => "ok",
          "output" => output_summary(addition)
        }

        {[provenance], [addition]}
      end
    else
      {[], []}
    end
  end

  defp recipe_review do
    fixture = LegacyImport.reviewed_recipe_fixture()

    %{
      "fixture" => "../phase5_kernel_recipe_replacements.json",
      "sha256" => "5522d0453cde53b8435551d4d410745ef66ac1de05d4dfe0fd310b39ba34af2d",
      "old_advertised_tags" => fixture["old_advertised_tags"],
      "new_advertised_tags" =>
        Enum.map(Antigen.Generators.KernelProbe.cover_cells(), fn {_, tag} -> Atom.to_string(tag) end),
      "menu_replacements" =>
        Enum.map(fixture["replacements"], &Map.take(&1, ["old_tag", "new_tag", "stored_record_retag_required"]))
    }
  end

  defp fresh_replay!(record) do
    paths = :code.get_path() |> Enum.reverse() |> Enum.flat_map(&["-pa", List.to_string(&1)])

    script = """
    {:ok, challenge} = Antigen.Corpus.decode_record(System.fetch_env!("ANTIGEN_MIGRATION_GUARD"))
    :ok = Antigen.Assays.Totality.run(challenge)
    """

    {diagnostics, status} =
      System.cmd(
        System.find_executable("elixir") || raise("elixir not found"),
        ["--erl", "+S 2:2"] ++ paths ++ ["-e", script],
        env: [{"ANTIGEN_MIGRATION_GUARD", record}],
        stderr_to_stdout: true
      )

    unless status == 0, do: raise("pending-sibling fresh-VM replay failed: " <> diagnostics)
    :ok
  end

  @doc "Construct new positive copies and unchanged-input rejection controls for reviewed rows."
  def inference_controls(%Challenge{kind: :typed_term, label: :well_typed, payload: original} = challenge) do
    env = SigMenu.env_of(original.sig)
    ctx = checked_context!(env, original.ctx)
    {:error, term_error} = Kernel.infer(ctx, original.term)
    {:error, claim_error} = Kernel.infer(ctx, original.type)

    negative =
      Challenge.new(
        kind: :malformed,
        assay: "term/rejection",
        label: :ill_typed,
        seed: challenge.seed,
        note: "Historical malformed Vec motive: original inference input retained",
        payload: Map.take(original, [:sig, :ctx, :term])
      )

    replacement = %{original | term: replacement_copy(original.term), type: replacement_copy(original.type)}

    positive = %{
      challenge
      | payload: replacement,
        note: "Separately checked replacement for archived historical Vec claim"
    }

    {:ok, {:vtype, _}} = Kernel.infer(ctx, replacement.type)
    {:ok, inferred} = Kernel.infer(ctx, replacement.term)
    :ok = Kernel.check(ctx, replacement.term, Eval.eval(replacement.type, Context.env(ctx)))

    {:ok, true} =
      Conv.conv_within?(
        Normalise.quote(inferred, Context.length(ctx)),
        replacement.type,
        Context.env(ctx),
        Context.length(ctx),
        env,
        Antigen.Assays.Term.assay_fuel()
      )

    nodes = cases_and_motives(replacement.term)
    Enum.each(nodes, fn {_kind, term} -> {:ok, _} = Kernel.infer(ctx, term) end)
    :ok = Runner.replay_one(negative)
    :ok = Runner.replay_one(positive)

    checks = %{
      "context_prefixes" => length(original.ctx),
      "original_term_rejection" => inspect(term_error),
      "original_claim_rejection" => inspect(claim_error),
      "positive_claim" => "ok",
      "positive_case" => "ok",
      "motives_checked" => Enum.count(nodes, fn {kind, _} -> kind == :motive end),
      "cases_checked" => Enum.count(nodes, fn {kind, _} -> kind == :case end)
    }

    {negative, positive, checks}
  end

  defp checked_context!(env, types) do
    Enum.reduce(Enum.reverse(types), Context.empty(env), fn type, ctx ->
      {:ok, {:vtype, _}} = Kernel.infer(ctx, type)
      Context.extend(ctx, Eval.eval(type, Context.env(ctx)))
    end)
  end

  # Restricted to these exact reviewed zero-parameter Vec annotation copies.
  # The original challenge and negative input never pass through this function.
  defp replacement_copy({:data, :Vec, [index], []}), do: {:data, :Vec, [], [replacement_copy(index)]}

  defp replacement_copy(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.map(&replacement_copy/1) |> List.to_tuple()

  defp replacement_copy(list) when is_list(list), do: Enum.map(list, &replacement_copy/1)
  defp replacement_copy(value), do: value

  # The five reviewed controls contain only nullary Bd branches: every nested
  # case and motive is independently inferable in the unchanged outer context.
  defp cases_and_motives({:case, scrut, motive, branches} = term) do
    unless Enum.all?(branches, fn {_name, arity, _body} -> arity == 0 end),
      do: raise("reviewed replacement contains a non-nullary branch")

    [{:case, term}, {:motive, motive}] ++
      cases_and_motives(scrut) ++
      Enum.flat_map(branches, fn {_name, 0, body} -> cases_and_motives(body) end)
  end

  defp cases_and_motives(_), do: []

  defp row_summary(row) do
    %{
      "source" => row.source,
      "line" => row.line,
      "sha256" => row.sha,
      "old_key64" => row.fields["key"],
      "old_kind" => row.fields["kind"],
      "old_assay" => row.fields["assay"],
      "old_label" => row.fields["label"],
      "disposition" => row.disposition,
      "actions" => row.actions,
      "error" => row.error,
      "outputs" => Enum.map(row.outputs, &output_summary/1)
    }
  end

  defp output_summary(output),
    do: %{"store" => output.target, "sha256" => sha(output.record), "key" => output.key, "replay" => output.replay}

  defp collisions(outputs) do
    outputs
    |> Enum.reject(&is_nil(&1.key))
    |> Enum.with_index(1)
    |> Enum.group_by(fn {output, _index} -> {output.target, output.key} end)
    |> Enum.filter(fn {_key, entries} -> length(entries) > 1 end)
    |> Enum.map(fn {{store, key}, entries} ->
      %{
        "store" => store,
        "key" => key,
        "output_ordinals" => Enum.map(entries, &elem(&1, 1)),
        "semantic_payloads" =>
          entries |> Enum.map(fn {o, _} -> Corpus.semantic_descriptor(o.challenge) end) |> Enum.uniq() |> length()
      }
    end)
    |> Enum.sort_by(&{&1["store"], &1["key"]})
  end

  @doc "Exact mutant fault/depth/carrier/wrapper counts for conservation evidence."
  def mutant_inventory(challenges) do
    mutants = Enum.filter(challenges, &(&1.kind == :mutant_term))

    %{
      "count" => length(mutants),
      "kinds" => counts(mutants, &Atom.to_string(&1.payload.fault.kind)),
      "depths" => counts(mutants, &to_string(Map.get(&1.payload.fault, :depth, 0))),
      "carriers" => counts(mutants, &inspect(Map.get(&1.payload.fault, :carrier))),
      "wrappers" =>
        mutants
        |> Enum.flat_map(&Map.get(&1.payload.fault, :wrap_path, []))
        |> Enum.frequencies()
        |> Map.new(fn {k, v} -> {Atom.to_string(k), v} end)
    }
  end

  defp counts(values, fun), do: values |> Enum.map(fun) |> Enum.frequencies()

  defp render([]), do: ""
  defp render(outputs), do: Enum.map_join(outputs, "\n", & &1.record) <> "\n"
  defp sha(binary), do: :crypto.hash(:sha256, binary) |> Base.encode16(case: :lower)

  defp validate_paths!(paths, opts) do
    if paths == [], do: raise(ArgumentError, "no input stores")

    if Enum.any?(paths, &(Path.basename(&1) == "retired.sexp")),
      do: raise(ArgumentError, "the existing retired store is inactive provenance, not migration input")

    if Enum.uniq(Enum.map(paths, &Path.basename/1)) != Enum.map(paths, &Path.basename/1),
      do: raise(ArgumentError, "input basename collision")

    archive = Keyword.get(opts, :archive_dir)
    out = Keyword.get(opts, :out_dir)
    inventory = Keyword.get(opts, :inventory)
    directories = Enum.reject([archive, out], &is_nil/1) |> Enum.map(&Path.expand/1)
    protected = inactive_paths(paths)

    protected_archives =
      if archive, do: Enum.map(protected, &Path.join(Path.expand(archive), Path.basename(&1))), else: []

    all =
      paths ++
        protected ++
        protected_archives ++
        Enum.map(paths, &(&1 <> ".antigen-migration")) ++
        Enum.flat_map(directories, fn dir -> Enum.map(paths, &Path.join(dir, Path.basename(&1))) end) ++
        if(inventory,
          do: Enum.map(["", ".tmp", ".publish.json", ".publish.json.tmp"], &(Path.expand(inventory) <> &1)),
          else: []
        )

    lexical = Enum.map(all, &Path.expand/1)
    resolved = Enum.map(all, &canonical/1)

    if length(Enum.uniq(lexical)) != length(lexical) or length(Enum.uniq(resolved)) != length(resolved),
      do: raise(ArgumentError, "input/archive/output/inventory paths alias")

    inodes =
      Enum.flat_map(all, fn path ->
        case File.stat(path) do
          {:ok, %{type: :regular, inode: inode, major_device: major, minor_device: minor}} when inode > 0 ->
            [{major, minor, inode}]

          {:ok, _} ->
            []

          {:error, :enoent} ->
            []

          {:error, reason} ->
            raise(File.Error, reason: reason, action: "stat", path: path)
        end
      end)

    if length(Enum.uniq(inodes)) != length(inodes),
      do: raise(ArgumentError, "input/archive/output/inventory inode aliases")

    if Enum.any?(directories, &(canonical(&1) in Enum.map(paths, fn path -> canonical(path) end))),
      do: raise(ArgumentError, "directory aliases an input file")

    :ok
  end

  defp canonical(path, hops \\ 0)
  defp canonical(_, hops) when hops > 40, do: raise(ArgumentError, "symlink resolution budget exceeded")
  defp canonical("/", _hops), do: "/"

  defp canonical(path, hops) do
    path = Path.expand(path)
    parent = canonical(Path.dirname(path), hops)
    resolved = Path.join(parent, Path.basename(path))

    case File.read_link(resolved) do
      {:ok, target} -> canonical(Path.expand(target, parent), hops + 1)
      {:error, :einval} -> resolved
      {:error, :enoent} -> resolved
      {:error, reason} -> raise(File.Error, reason: reason, action: "resolve", path: resolved)
    end
  end

  defp preserve!(path, bytes) do
    case File.read(path) do
      {:ok, ^bytes} -> :ok
      {:ok, _} -> raise("refusing to overwrite differing archive/staged file #{path}")
      {:error, :enoent} -> File.write!(path, bytes, [:exclusive, :sync])
      {:error, reason} -> raise(File.Error, reason: reason, action: "read", path: path)
    end
  end

  defp write_json!(path, value) do
    File.mkdir_p!(Path.dirname(path))
    tmp = path <> ".tmp"
    File.write!(tmp, [:json.encode(value), "\n"], [:exclusive, :sync])
    File.rename!(tmp, path)
  end
end
