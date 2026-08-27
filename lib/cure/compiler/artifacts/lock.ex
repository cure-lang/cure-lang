defmodule Cure.Compiler.Artifacts.Lock do
  @moduledoc false

  require Logger

  @lock_name ".cure_artifact.lock"
  @owner_key {__MODULE__, :owner}

  @spec with_lock(Path.t(), (-> result)) :: result | {:error, term()} when result: term()
  def with_lock(output_root, fun) when is_function(fun, 0) do
    if match?({:ok, %File.Stat{type: :symlink}}, File.lstat(output_root)) and not File.exists?(output_root) do
      File.rm_rf!(output_root)
    end

    File.mkdir_p!(output_root)
    path = Path.join(output_root, @lock_name)

    case acquire(path) do
      {:ok, handle} ->
        owner = lock_owner(path)
        write_owner(path, owner)
        Process.put(@owner_key, {handle, path, owner})

        try do
          fun.()
        after
          Process.delete(@owner_key)
          release(handle)
        end

      {:error, reason} ->
        {:error, {:artifact_lock_failed, reason}}
    end
  end

  @doc false
  @spec set_intended_generation(binary()) :: :ok
  def set_intended_generation(generation) when is_binary(generation) do
    case Process.get(@owner_key) do
      {handle, path, owner} ->
        owner = Map.put(owner, :intended_generation, generation)
        write_owner(path, owner)
        Process.put(@owner_key, {handle, path, owner})
        :ok

      nil ->
        :ok
    end
  end

  defp acquire(path) do
    case kernel_lock_command(path) do
      {:ok, executable, args} -> acquire_kernel(executable, args, path)
      :unavailable -> {:error, :kernel_file_lock_unavailable}
    end
  end

  # SwiftPM uses flock(2) on Unix and LockFileEx on Windows. Use the platform's
  # standard flock frontend as a tiny port owner: the child prints only after
  # the kernel lock is held, then remains alive reading its stdin. Closing the
  # port exits the child and the kernel releases the lock, including when the
  # BEAM crashes. Ownership never depends on deleting the path, avoiding
  # marker-file ABA races. A non-blocking probe lets us report the current
  # owner before waiting indefinitely for a legitimate long-running writer.
  defp acquire_kernel(executable, args, path) do
    port =
      Port.open({:spawn_executable, executable}, [
        :binary,
        :exit_status,
        :use_stdio,
        {:line, 1_024},
        {:args, args}
      ])

    await_kernel_lock(port, path)
  rescue
    error -> {:error, {:kernel_lock, Exception.message(error)}}
  end

  defp await_kernel_lock(port, path) do
    receive do
      {^port, {:data, {:eol, "CURE_LOCK_BUSY"}}} ->
        log_waiting_owner(path)
        await_kernel_lock(port, path)

      {^port, {:data, {:eol, "CURE_LOCK_ACQUIRED"}}} ->
        {:ok, {:kernel, port}}

      {^port, {:exit_status, status}} ->
        {:error, {:kernel_lock_exited, status}}
    end
  end

  defp kernel_lock_command(path) do
    shell = System.find_executable("sh")
    lockf = System.find_executable("lockf")
    flock = System.find_executable("flock")

    cond do
      shell && lockf ->
        script =
          "exec 9>>\"$1\" || exit 73; " <>
            "if \"$2\" -s -t 0 9; then :; " <>
            "else printf 'CURE_LOCK_BUSY\\n'; \"$2\" -s 9 || exit 75; fi; " <>
            "printf 'CURE_LOCK_ACQUIRED\\n'; IFS= read -r _"

        {:ok, shell, ["-c", script, "cure-artifact-lock", path, lockf]}

      shell && flock ->
        script =
          "exec 9>>\"$1\" || exit 73; " <>
            "if \"$2\" -n 9; then :; " <>
            "else printf 'CURE_LOCK_BUSY\\n'; \"$2\" 9 || exit 75; fi; " <>
            "printf 'CURE_LOCK_ACQUIRED\\n'; IFS= read -r _"

        {:ok, shell, ["-c", script, "cure-artifact-lock", path, flock]}

      true ->
        :unavailable
    end
  end

  defp release({:kernel, port}) do
    if Port.info(port) do
      Port.command(port, "release\n")

      receive do
        {^port, {:exit_status, _status}} -> :ok
      after
        1_000 -> safe_port_close(port)
      end

      # Receiving the child exit status and closing the BEAM-side handle are
      # distinct operations. Discard the port handle deterministically.
      safe_port_close(port)
    end

    :ok
  catch
    :error, :badarg -> :ok
  end

  defp safe_port_close(port) do
    if Port.info(port), do: Port.close(port)
    :ok
  catch
    :error, :badarg -> :ok
  end

  defp lock_owner(path) do
    %{
      node: to_string(node()),
      pid: inspect(self()),
      os_pid: System.pid(),
      host: hostname(),
      acquired_at: System.os_time(:second),
      output_root: Path.dirname(path),
      intended_generation: :pending
    }
  end

  defp log_waiting_owner(path) do
    owner = read_owner(path)

    Logger.info(fn ->
      case owner do
        %{os_pid: os_pid, output_root: output_root} = details ->
          generation = Map.get(details, :intended_generation, :pending)

          "another Cure compiler (OS PID #{os_pid}) is publishing artifacts to " <>
            "#{output_root}; waiting for generation #{inspect(generation)} to finish"

        _ ->
          "another Cure compiler is publishing artifacts; waiting for it to finish"
      end
    end)
  end

  defp read_owner(path) do
    with {:ok, binary} <- File.read(path),
         owner when is_map(owner) <- :erlang.binary_to_term(binary, [:safe]) do
      owner
    else
      _ -> nil
    end
  rescue
    _ -> nil
  end

  defp write_owner(path, owner) do
    File.write!(path, :erlang.term_to_binary(owner, [:deterministic]), [:sync])
  end

  defp hostname do
    case :inet.gethostname() do
      {:ok, host} -> List.to_string(host)
      {:error, _} -> "unknown"
    end
  end
end
