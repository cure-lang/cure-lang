defmodule CurePool.PoolTest do
  use ExUnit.Case, async: true

  setup do
    {:ok, pool} = CurePool.start_pool(capacity: 2)
    %{pool: pool}
  end

  test "a fresh pool has every slot available", %{pool: pool} do
    assert CurePool.stats(pool) == %{capacity: 2, available: 2, in_use: 0}
  end

  test "checkout moves a slot from available to in_use", %{pool: pool} do
    assert {:ok, _lease} = CurePool.checkout(pool)
    assert CurePool.stats(pool) == %{capacity: 2, available: 1, in_use: 1}
  end

  test "run executes the task on the leased worker", %{pool: pool} do
    {:ok, lease} = CurePool.checkout(pool)

    assert {:ok, worker} = CurePool.run(lease, fn w -> w end)
    assert is_pid(worker)
    assert worker == lease.worker
    assert Process.alive?(worker)
  end

  test "checkin restores the slot", %{pool: pool} do
    {:ok, lease} = CurePool.checkout(pool)
    assert :ok = CurePool.checkin(pool, lease)
    assert CurePool.stats(pool) == %{capacity: 2, available: 2, in_use: 0}
  end

  test "an exhausted pool refuses checkout", %{pool: pool} do
    assert {:ok, _a} = CurePool.checkout(pool)
    assert {:ok, _b} = CurePool.checkout(pool)
    assert {:error, :empty} = CurePool.checkout(pool)
    assert CurePool.stats(pool) == %{capacity: 2, available: 0, in_use: 2}
  end

  test "checking in twice is a stale error, never a double-free", %{pool: pool} do
    {:ok, lease} = CurePool.checkout(pool)
    assert :ok = CurePool.checkin(pool, lease)
    assert {:error, :stale} = CurePool.checkin(pool, lease)
    assert CurePool.stats(pool) == %{capacity: 2, available: 2, in_use: 0}
  end

  test "the count is invariant across many checkouts and checkins", %{pool: pool} do
    for _ <- 1..5 do
      {:ok, lease} = CurePool.checkout(pool)
      {:ok, _} = CurePool.run(lease, fn w -> w end)
      :ok = CurePool.checkin(pool, lease)
    end

    assert CurePool.stats(pool) == %{capacity: 2, available: 2, in_use: 0}
  end
end
