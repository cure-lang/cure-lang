defmodule Cure.Compiler.Artifacts.Writer do
  @moduledoc """
  Stages complete artifact sets and publishes immutable generations.

  The caller-visible output directory is a container. Its `current` file names
  one directory below `.cure_generations/`; readers resolve that pointer before
  opening a manifest. Candidate files never overwrite the currently published
  generation.
  """

  alias Cure.Compiler.Artifacts
  alias Cure.Compiler.Artifacts.Lock

  @generations ".cure_generations"
  @current "current"

  @spec transact(Path.t(), (Path.t() -> {:ok, term()} | {:error, term()})) ::
          {:ok, term()} | {:error, term()}
  def transact(output_root, build) when is_function(build, 1) do
    Lock.with_lock(output_root, fn ->
      cleanup_staging(output_root)
      stage = stage_path(output_root)
      File.mkdir_p!(stage)

      try do
        copy_current(output_root, stage)

        case build.(stage) do
          {:ok, result} ->
            case publish(stage, output_root) do
              {:ok, generation_root} -> {:ok, attach_generation_root(result, generation_root)}
              {:error, _} = error -> error
            end

          {:no_publish, result} ->
            {:ok, result}

          {:error, _} = error ->
            error
        end
      after
        File.rm_rf(stage)
      end
    end)
  end

  @spec copy_verified(Path.t(), Path.t()) :: {:ok, Path.t()} | {:error, term()}
  def copy_verified(source_root, output_root) do
    with {:ok, source} <- Artifacts.open_verified_set(source_root, verification: :full) do
      Lock.with_lock(output_root, fn ->
        cleanup_staging(output_root)
        stage = stage_path(output_root)
        File.mkdir_p!(stage)

        try do
          for path <-
                Path.wildcard(Path.join(source.artifact_root, "*")) ++
                  [
                    Path.join(
                      source.artifact_root,
                      Cure.Compiler.BuildManifest.filename()
                    )
                  ],
              File.regular?(path) do
            File.cp!(path, Path.join(stage, Path.basename(path)))
          end

          publish(stage, output_root)
        after
          File.rm_rf(stage)
        end
      end)
    end
  end

  @spec resolve(Path.t()) :: Path.t()
  def resolve(output_root) do
    pointer = Path.join(output_root, @current)

    with {:ok, generation} <- File.read(pointer),
         generation = String.trim(generation),
         true <- valid_generation_name?(generation),
         root = Path.join([output_root, @generations, generation]),
         true <- File.dir?(root) do
      root
    else
      _ -> output_root
    end
  end

  defp copy_current(output_root, stage) do
    current = resolve(output_root)

    case Cure.Compiler.BuildManifest.read(current) do
      {:ok, _manifest} ->
        current
        |> Path.join("*.beam")
        |> Path.wildcard()
        |> Enum.each(fn artifact_path ->
          File.cp!(artifact_path, Path.join(stage, Path.basename(artifact_path)))
        end)

        File.cp!(
          Path.join(current, Cure.Compiler.BuildManifest.filename()),
          Path.join(stage, Cure.Compiler.BuildManifest.filename())
        )

      {:error, _reason} ->
        :ok
    end
  rescue
    _ -> :ok
  end

  defp publish(stage, output_root) do
    with {:ok, manifest} <- Artifacts.open_verified_set(stage, verification: :full) do
      generation = Base.encode16(manifest.artifact_digest, case: :lower)
      generations = Path.join(output_root, @generations)
      destination = Path.join(generations, generation)
      File.mkdir_p!(generations)

      install_generation(stage, destination)

      :ok = publish_pointer(output_root, generation)
      remove_legacy_outputs(output_root)
      {:ok, destination}
    end
  end

  defp install_generation(stage, destination) do
    cond do
      not File.dir?(destination) ->
        File.rename!(stage, destination)

      match?({:ok, _}, Artifacts.open_verified_set(destination)) ->
        :ok

      true ->
        quarantine =
          destination <> ".corrupt.#{System.unique_integer([:positive, :monotonic])}"

        File.rename!(destination, quarantine)

        try do
          File.rename!(stage, destination)
        after
          File.rm_rf(quarantine)
        end
    end
  end

  defp publish_pointer(output_root, generation) do
    pointer = Path.join(output_root, @current)
    temporary = pointer <> ".#{System.unique_integer([:positive])}.tmp"
    File.write!(temporary, generation <> "\n", [:sync])
    File.rename(temporary, pointer)
  end

  defp remove_legacy_outputs(output_root) do
    for path <- Path.wildcard(Path.join(output_root, "Cure.*.beam")) do
      File.rm(path)
    end

    File.rm(Path.join(output_root, Cure.Compiler.BuildManifest.filename()))
    :ok
  end

  defp stage_path(output_root) do
    Path.join(
      output_root,
      ".cure_staging_#{System.unique_integer([:positive, :monotonic])}"
    )
  end

  defp cleanup_staging(output_root) do
    output_root
    |> Path.join(".cure_staging_*")
    |> Path.wildcard(match_dot: true)
    |> Enum.each(&File.rm_rf/1)
  end

  defp valid_generation_name?(generation) do
    byte_size(generation) == 64 and String.match?(generation, ~r/\A[0-9a-f]{64}\z/)
  end

  defp attach_generation_root(result, root) when is_map(result),
    do: Map.put(result, :artifact_root, root)

  defp attach_generation_root(result, _root), do: result
end
