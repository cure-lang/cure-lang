defmodule CureExchangeTest do
  use ExUnit.Case, async: true

  alias CureExchange.Money

  # ============================================================================
  # Raw FSM (gen_statem) tests
  #
  # `cure_src/escrow_fsm.cure` compiles to exactly this module and nothing
  # else -- see its header comment. Every edge, the guard, and stray-event
  # safety are exercised directly against it here, the same way
  # `cure_turnstile/test/cure_turnstile_test.exs` tests its FSM.
  # ============================================================================

  describe "raw Cure.Main.EscrowFsm gen_statem" do
    @fsm :"Cure.Main.EscrowFsm"
    @fresh_data {:EscrowData, 0, :none, :none, 0}

    test "start_link/1 initializes in Created" do
      {:ok, pid} = @fsm.start_link(@fresh_data)
      assert {:Created, @fresh_data} = :sys.get_state(pid)
      :gen_statem.stop(pid)
    end

    test "LockFunds with a positive amount reserves funds" do
      {:ok, pid} = @fsm.start_link(@fresh_data)
      :gen_statem.cast(pid, {:LockFunds, 500, :"Q-1"})
      assert {:FundsReserved, {:EscrowData, 500, :"Q-1", :none, 0}} = :sys.get_state(pid)
      :gen_statem.stop(pid)
    end

    test "LockFunds with a non-positive amount is rejected by the guard" do
      {:ok, pid} = @fsm.start_link(@fresh_data)
      :gen_statem.cast(pid, {:LockFunds, 0, :"Q-1"})
      assert {:Created, @fresh_data} = :sys.get_state(pid)
      :gen_statem.stop(pid)
    end

    test "the full happy path: LockFunds -> CounterpartyMatched -> BankConfirmed" do
      {:ok, pid} = @fsm.start_link(@fresh_data)
      :gen_statem.cast(pid, {:LockFunds, 500, :"Q-1"})
      :gen_statem.cast(pid, {:CounterpartyMatched, :"T-1"})
      assert {:ExecutingSwap, {:EscrowData, 500, :"Q-1", :"T-1", 0}} = :sys.get_state(pid)
      :gen_statem.cast(pid, :BankConfirmed)
      assert {:Completed, _} = :sys.get_state(pid)
      :gen_statem.stop(pid)
    end

    test "QuoteExpired cancels a reserved (unmatched) escrow" do
      {:ok, pid} = @fsm.start_link(@fresh_data)
      :gen_statem.cast(pid, {:LockFunds, 500, :"Q-1"})
      :gen_statem.cast(pid, :QuoteExpired)
      assert {:Cancelled, _} = :sys.get_state(pid)
      :gen_statem.stop(pid)
    end

    test "BankFailed and SettleTimeout both move a matched escrow to Refunding" do
      for event <- [:BankFailed, :SettleTimeout] do
        {:ok, pid} = @fsm.start_link(@fresh_data)
        :gen_statem.cast(pid, {:LockFunds, 500, :"Q-1"})
        :gen_statem.cast(pid, {:CounterpartyMatched, :"T-1"})
        :gen_statem.cast(pid, event)
        assert {:Refunding, _} = :sys.get_state(pid)
        :gen_statem.cast(pid, :RefundCompleted)
        assert {:Refunded, _} = :sys.get_state(pid)
        :gen_statem.stop(pid)
      end
    end

    test "a stray event with no matching row is a safe no-op, on every terminal state" do
      for terminal <- [:Cancelled, :Completed, :Refunded] do
        {:ok, pid} = @fsm.start_link(@fresh_data)
        :sys.replace_state(pid, fn _ -> {terminal, @fresh_data} end)
        :gen_statem.cast(pid, :BankConfirmed)
        assert {^terminal, @fresh_data} = :sys.get_state(pid)
        :gen_statem.stop(pid)
      end
    end

    test "a late QuoteExpired after matching does not cancel an in-flight swap" do
      {:ok, pid} = @fsm.start_link(@fresh_data)
      :gen_statem.cast(pid, {:LockFunds, 500, :"Q-1"})
      :gen_statem.cast(pid, {:CounterpartyMatched, :"T-1"})
      :gen_statem.cast(pid, :QuoteExpired)
      assert {:ExecutingSwap, _} = :sys.get_state(pid)
      :gen_statem.stop(pid)
    end
  end

  # ============================================================================
  # CureExchange / TradeWorker integration tests
  #
  # These drive the whole stack: Ledger effects, timers, and the simulated
  # bank webhook, through the public `CureExchange` facade.
  # ============================================================================

  setup do
    account_id = System.unique_integer([:positive])
    :ok = CureExchange.open_account(account_id, "Test Account", 1_000_000, :usd)
    %{account_id: account_id}
  end

  test "happy path: bank confirms, funds are captured", %{account_id: account_id} do
    {:ok, pid, _quote_id} =
      CureExchange.open_trade(account_id, :usd, 10_000, bank_delay_ms: 10, settle_ttl_ms: 1_000)

    CureExchange.match_counterparty(pid, :"T-happy")

    assert %{state: :Completed} = wait_for_state(pid, :Completed)
    assert {:ok, %Money{amount: 0, currency: :usd}} = CureExchange.held(account_id)
    assert {:ok, %Money{amount: 990_000, currency: :usd}} = CureExchange.balance(account_id)
  end

  test "quote expiry: the hold is released and the escrow is cancelled", %{account_id: account_id} do
    {:ok, pid, _quote_id} = CureExchange.open_trade(account_id, :usd, 5_000, quote_ttl_ms: 10)

    assert %{state: :Cancelled} = wait_for_state(pid, :Cancelled)
    assert {:ok, %Money{amount: 0, currency: :usd}} = CureExchange.held(account_id)
    assert {:ok, %Money{amount: 1_000_000, currency: :usd}} = CureExchange.balance(account_id)
  end

  test "bank failure: the multi-step rollback refunds the hold", %{account_id: account_id} do
    {:ok, pid, _quote_id} =
      CureExchange.open_trade(account_id, :usd, 7_500, bank_delay_ms: 10, bank_outcome: :failed, settle_ttl_ms: 1_000)

    CureExchange.match_counterparty(pid, :"T-failed")

    assert %{state: :Refunded} = wait_for_state(pid, :Refunded)
    assert {:ok, %Money{amount: 0, currency: :usd}} = CureExchange.held(account_id)
    assert {:ok, %Money{amount: 1_000_000, currency: :usd}} = CureExchange.balance(account_id)
  end

  test "settle timeout: the bank never answers, the safety net refunds the hold", %{account_id: account_id} do
    {:ok, pid, _quote_id} =
      CureExchange.open_trade(account_id, :usd, 2_500, bank_delay_ms: 10_000, settle_ttl_ms: 10)

    CureExchange.match_counterparty(pid, :"T-timeout")

    assert %{state: :Refunded} = wait_for_state(pid, :Refunded)
    assert {:ok, %Money{amount: 1_000_000, currency: :usd}} = CureExchange.balance(account_id)
  end

  test "a late quote-expiry timer after a match is a safe no-op", %{account_id: account_id} do
    {:ok, pid, _quote_id} =
      CureExchange.open_trade(account_id, :usd, 1_000, quote_ttl_ms: 1_000, bank_delay_ms: 10, settle_ttl_ms: 1_000)

    # match before the quote-expiry timer fires
    CureExchange.match_counterparty(pid, :"T-race")
    assert %{state: :Completed} = wait_for_state(pid, :Completed)

    # deliver a late :quote_expired message after completion and verify it is a no-op
    send(pid, :quote_expired)
    assert %{state: :Completed} = CureExchange.status(pid)
    # the hold was captured, not released twice or double-refunded
    assert {:ok, %Money{amount: 0, currency: :usd}} = CureExchange.held(account_id)
    assert {:ok, %Money{amount: 999_000, currency: :usd}} = CureExchange.balance(account_id)
  end

  test "reserving more than the account's balance fails to open the trade", %{account_id: account_id} do
    assert {:error, {:reserve_failed, _reason}} =
             CureExchange.open_trade(account_id, :usd, 10_000_000)
  end

  # Poll until `CureExchange.status(pid)` reaches `expected_state` (or the
  # bounded wait elapses). Avoids bare `:timer.sleep` races on slower CI
  # runners while still returning the actual status for ExUnit's assertion.
  defp wait_for_state(pid, expected_state, attempts \\ 200)

  defp wait_for_state(pid, _expected_state, 0), do: CureExchange.status(pid)

  defp wait_for_state(pid, expected_state, attempts) do
    case CureExchange.status(pid) do
      %{state: ^expected_state} = status ->
        status

      _other ->
        Process.sleep(10)
        wait_for_state(pid, expected_state, attempts - 1)
    end
  end
end
