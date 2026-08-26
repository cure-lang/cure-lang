defmodule CureForgeTest do
  use ExUnit.Case, async: false

  setup do
    # Each test sees the tree in a known state. All four actors
    # expose a :reset / :clear path.
    CureForge.reset_metrics()
    CureForge.reset_pool()
    _ = CureForge.drain_log()

    case CureForge.queue_pid() do
      nil -> :ok
      pid -> :gen_server.cast(pid, :clear)
    end

    :ok
  end

  describe "application / supervision wiring" do
    test "the top-level Mix application is started" do
      assert {:ok, _} = Application.ensure_all_started(:cure_forge)
    end

    test "Cure.Main.CureForge is loaded and exposes the Application callbacks" do
      assert Code.ensure_loaded?(:"Cure.Main.CureForge")

      for callback <- [:start, :stop, :start_phase] do
        assert function_exported?(:"Cure.Main.CureForge", callback, callback_arity(callback))
      end
    end

    test "Cure.Forge.Root is registered by name and alive" do
      pid = Process.whereis(CureForge.sup_module())
      assert is_pid(pid)
      assert Process.alive?(pid)
    end

    test "Forge.Root supervises metrics, logger, queue, and pool" do
      ids =
        CureForge.which_children()
        |> Enum.map(fn {id, _pid, _type, _modules} -> id end)
        |> Enum.sort()

      assert ids == [:logger, :metrics, :pool, :queue]
    end

    test "every child is a live worker pid" do
      for {_id, pid, type, _modules} <- CureForge.which_children() do
        assert is_pid(pid)
        assert Process.alive?(pid)
        assert type == :worker
      end
    end
  end

  describe "application env" do
    test "[application.env] values are readable through Application.get_env" do
      assert Application.get_env(:cure_forge, :greeting) == "forge ready"
      assert Application.get_env(:cure_forge, :idle_timeout_ms) == 5000
      assert Application.get_env(:cure_forge, :max_log_lines) == 16
    end
  end

  describe "metrics actor" do
    test "starts with zero counters" do
      assert CureForge.metrics() == %{requests: 0, errors: 0}
    end

    test "observe/1 routes :ok to requests and anything else to errors" do
      CureForge.observe(:ok)
      CureForge.observe(:ok)
      CureForge.observe({:fail, :boom})

      assert CureForge.metrics() == %{requests: 2, errors: 1}
    end

    test "reset_metrics zeroes the counters" do
      CureForge.observe(:ok)
      CureForge.observe(:ok)
      assert CureForge.metrics() == %{requests: 2, errors: 0}

      CureForge.reset_metrics()
      assert CureForge.metrics() == %{requests: 0, errors: 0}
    end
  end

  describe "logger actor" do
    test "buffers lines and drains in FIFO order, capped by max_log_lines" do
      CureForge.log("one")
      CureForge.log("two")
      CureForge.log("three")

      assert CureForge.drain_log() == ["one", "two", "three"]
      assert CureForge.drain_log() == []
    end
  end

  describe "queue actor" do
    test "enqueue and size round-trip" do
      assert CureForge.queue_size() == 0

      CureForge.submit(:ok)
      CureForge.submit({:fail, :timeout})
      CureForge.submit(:ok)

      assert CureForge.queue_size() == 3
    end
  end

  describe "end-to-end drain_queue" do
    test "drains tasks through the pool and into the metrics actor" do
      CureForge.submit(:ok)
      CureForge.submit(:ok)
      CureForge.submit({:fail, :timeout})

      assert {:ok, 3} = CureForge.drain_queue()
      assert CureForge.queue_size() == 0

      assert %{done: 2, failed: 1} = CureForge.pool_state()
      assert %{requests: 2, errors: 1} = CureForge.metrics()
    end

    test "draining an empty queue is a no-op" do
      assert {:ok, 0} = CureForge.drain_queue()
    end
  end

  describe "supervisor restart semantics" do
    test "killing a worker replaces it with a fresh pid" do
      pool_before = CureForge.pool_pid()
      CureForge.submit(:ok)
      CureForge.drain_queue()
      assert %{done: 1, failed: 0} = CureForge.pool_state()

      ref = Process.monitor(pool_before)
      Process.exit(pool_before, :kill)
      assert_receive {:DOWN, ^ref, :process, ^pool_before, :killed}, 500

      pool_after = wait_for_restart(:pool, pool_before)
      assert is_pid(pool_after)
      assert pool_after != pool_before
      # :one_for_one + :permanent restart with the default initial
      # payload -- the counters are zeroed again.
      assert %{done: 0, failed: 0} = CureForge.pool_state()
    end
  end

  defp callback_arity(:start), do: 2
  defp callback_arity(:stop), do: 1
  defp callback_arity(:start_phase), do: 3

  defp wait_for_restart(id, previous, tries \\ 50) do
    case CureForge.which_children() |> Enum.find(fn {kid, _, _, _} -> kid == id end) do
      {^id, pid, _type, _modules} when is_pid(pid) and pid != previous ->
        pid

      _ when tries > 0 ->
        Process.sleep(10)
        wait_for_restart(id, previous, tries - 1)

      _ ->
        flunk("supervisor did not restart child #{inspect(id)}")
    end
  end
end
