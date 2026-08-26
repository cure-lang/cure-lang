defmodule CureColonyTest do
  use ExUnit.Case, async: false

  setup do
    # Each test sees the tree in a known state. The workers are
    # idempotent under `:reset`, and the echo actor carries whatever
    # the last test left behind unless we wipe it.
    CureColony.reset(CureColony.worker_a())
    CureColony.reset(CureColony.worker_b())
    CureColony.echo_message(nil)
    :ok
  end

  describe "application / supervision wiring" do
    test "Cure.Colony is registered by name and alive" do
      pid = Process.whereis(CureColony.sup_module())
      assert is_pid(pid)
      assert Process.alive?(pid)
    end

    test "Colony supervises worker_a, worker_b, and echo" do
      ids =
        CureColony.which_children()
        |> Enum.map(fn {id, _pid, _type, _modules} -> id end)
        |> Enum.sort()

      assert ids == [:echo, :worker_a, :worker_b]
    end

    test "each direct child is a live pid" do
      for {_id, pid, _type, _modules} <- CureColony.which_children() do
        assert is_pid(pid)
        assert Process.alive?(pid)
      end
    end

    test "worker_a and worker_b are different processes" do
      assert CureColony.worker_a() != CureColony.worker_b()
    end
  end

  describe "worker actor" do
    test "starts at zero" do
      assert CureColony.worker_state(CureColony.worker_a()) == 0
      assert CureColony.worker_state(CureColony.worker_b()) == 0
    end

    test "inc increments the counter" do
      worker = CureColony.worker_a()

      CureColony.inc(worker)
      CureColony.inc(worker)
      CureColony.inc(worker)

      assert CureColony.worker_state(worker) == 3
    end

    test "reset returns the counter to zero" do
      worker = CureColony.worker_a()

      CureColony.inc(worker)
      CureColony.inc(worker)
      assert CureColony.worker_state(worker) == 2

      CureColony.reset(worker)
      assert CureColony.worker_state(worker) == 0
    end

    test "worker_a and worker_b maintain independent state" do
      wa = CureColony.worker_a()
      wb = CureColony.worker_b()

      CureColony.inc(wa)
      CureColony.inc(wa)
      CureColony.inc(wb)

      assert CureColony.worker_state(wa) == 2
      assert CureColony.worker_state(wb) == 1
    end
  end

  describe "echo actor" do
    test "stores the last message it received as its payload" do
      CureColony.echo_message(:ping)
      assert CureColony.echo_state() == :ping

      CureColony.echo_message(%{k: :v})
      assert CureColony.echo_state() == %{k: :v}

      CureColony.echo_message("hello")
      assert CureColony.echo_state() == "hello"
    end
  end

  describe "supervisor restart semantics" do
    test "kill worker_a and it is restarted with a fresh counter" do
      wa_before = CureColony.worker_a()
      CureColony.inc(wa_before)
      CureColony.inc(wa_before)
      assert CureColony.worker_state(wa_before) == 2

      ref = Process.monitor(wa_before)
      Process.exit(wa_before, :kill)
      assert_receive {:DOWN, ^ref, :process, ^wa_before, :killed}, 500

      # :one_for_one + default :permanent restart: a new worker_a is
      # spawned and given the actor's default initial payload (0).
      wa_after = wait_for_restart(:worker_a, wa_before)
      assert is_pid(wa_after)
      assert wa_after != wa_before
      assert CureColony.worker_state(wa_after) == 0
    end
  end

  # Poll `Supervisor.which_children/1` until the child with id `id`
  # points to a pid that differs from `previous`. Guards against the
  # race between `Process.exit(pid, :kill)` and the supervisor's
  # own `:DOWN` handling.
  defp wait_for_restart(id, previous, tries \\ 50) do
    case CureColony.which_children() |> Enum.find(fn {kid, _, _, _} -> kid == id end) do
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
