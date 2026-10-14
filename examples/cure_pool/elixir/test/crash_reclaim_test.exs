defmodule CurePool.CrashReclaimTest do
  @moduledoc """
  The runtime guarantee the brief calls out: **a crash while holding a lease
  does not strand a slot.**

  This is the failure mode ordinary pools get wrong -- a client checks a worker
  out, dies, and the worker is never returned. Here the pool monitors the
  holder and reclaims the slot the moment it goes down, so `available + in_use`
  is invariant across the crash.
  """

  use ExUnit.Case, async: true

  setup do
    {:ok, pool} = CurePool.start_pool(capacity: 2)
    %{pool: pool}
  end

  test "a client that dies mid-lease has its slot reclaimed", %{pool: pool} do
    # A short-lived process checks out a lease and then dies without returning.
    holder =
      spawn(fn ->
        {:ok, _lease} = CurePool.checkout(pool)
        # The holder now blocks forever, holding the lease, until we kill it.
        Process.sleep(:infinity)
      end)

    # Wait until the checkout has landed.
    wait_until(fn -> CurePool.stats(pool).in_use == 1 end)
    assert CurePool.stats(pool) == %{capacity: 2, available: 1, in_use: 1}

    # Kill the holder -- the crash the pool must survive.
    Process.exit(holder, :kill)

    # The pool reclaims the slot: back to fully available.
    wait_until(fn -> CurePool.stats(pool).available == 2 end)
    assert CurePool.stats(pool) == %{capacity: 2, available: 2, in_use: 0}
  end

  test "a crashed worker is replaced, keeping capacity constant", %{pool: pool} do
    {:ok, lease} = CurePool.checkout(pool)
    worker = lease.worker

    # Kill the *worker* while it is checked out.
    Process.exit(worker, :kill)

    # The pool notices, drops the dead worker, and starts a replacement: the
    # capacity is preserved even though a resource was lost.
    wait_until(fn -> CurePool.stats(pool).available == 2 end)
    assert CurePool.stats(pool) == %{capacity: 2, available: 2, in_use: 0}

    # And the pool is still usable with a fresh worker.
    {:ok, new_lease} = CurePool.checkout(pool)
    refute new_lease.worker == worker
    assert {:ok, fresh} = CurePool.run(new_lease, fn w -> w end)
    assert Process.alive?(fresh)
  end

  test "many concurrent holders crashing never leak a slot", %{pool: pool} do
    holders =
      for _ <- 1..2 do
        spawn(fn ->
          {:ok, _lease} = CurePool.checkout(pool)
          Process.sleep(:infinity)
        end)
      end

    wait_until(fn -> CurePool.stats(pool).in_use == 2 end)
    assert CurePool.stats(pool).available == 0

    Enum.each(holders, &Process.exit(&1, :kill))

    wait_until(fn -> CurePool.stats(pool).available == 2 end)
    assert CurePool.stats(pool) == %{capacity: 2, available: 2, in_use: 0}
  end

  # Poll until `pred` holds, or fail after a bounded number of tries. Avoids a
  # bare `Process.sleep` race while keeping the tests deterministic.
  defp wait_until(pred, tries \\ 100)

  defp wait_until(_pred, 0), do: flunk("condition never became true")

  defp wait_until(pred, tries) do
    if pred.() do
      :ok
    else
      Process.sleep(10)
      wait_until(pred, tries - 1)
    end
  end
end
