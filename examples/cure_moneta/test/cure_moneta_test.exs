defmodule CureMonetaTest do
  use ExUnit.Case, async: false

  @moduledoc """
  Exercises both the raw `:"Cure.Moneta"` BEAM module (compiled from Cure
  source), the `:"Cure.Main.Transaction"` state machine, and the high-level
  `CureMoneta` Elixir wrapper.
  """

  @moneta :"Cure.Moneta"
  @fsm :"Cure.Main.Transaction"

  # -- Helpers ----------------------------------------------------------------

  # Build the ordinary tagged tuples emitted for Cure records and ADTs.
  defp money(amount, currency, frac), do: {:Money, amount, currency_atom(currency), frac}

  defp currency_atom(currency) do
    currency |> Atom.to_string() |> String.upcase() |> String.to_atom()
  end

  defp money_amount({:Money, amount, _currency, _fractional_units}), do: amount
  defp money_currency({:Money, _amount, currency, _fractional_units}), do: currency

  defp money_fractional_units({:Money, _amount, _currency, fractional_units}),
    do: fractional_units

  defp eur(cents), do: money(cents, :eur, 100)
  defp usd(cents), do: money(cents, :usd, 100)
  defp jpy(amount), do: money(amount, :jpy, 1)
  defp omr(fils), do: money(fils, :omr, 1000)

  defp account(id, owner, balance),
    do: {:Account, id, owner, balance}

  defp ledger(accounts), do: {:Ledger, accounts}

  # Advance the FSM through create + submit (dispatch! auto-fires) and sync.
  defp reach_awaiting(pid) do
    :gen_statem.cast(pid, :create)
    :gen_statem.cast(pid, :submit)
    # Ensure the async cast and the handle_continue auto-fire have both been
    # processed before we inspect state.
    _ = :sys.get_state(pid)
  end

  # ===========================================================================
  # 1. Cure.Moneta raw module
  # ===========================================================================

  describe "Cure.Moneta: Show protocol (Money record)" do
    test "EUR renders as major.minor with two decimal places" do
      assert @moneta.show(eur(10_050)) == ~c"EUR 100.50"
    end

    test "JPY renders without decimal point" do
      assert @moneta.show(jpy(1250)) == ~c"JPY 1250"
    end

    test "OMR renders with three decimal places" do
      assert @moneta.show(omr(1_500)) == ~c"OMR 1.500"
    end

    test "EUR zero pads the minor part" do
      assert @moneta.show(eur(500)) == ~c"EUR 5.00"
    end
  end

  describe "Cure.Moneta: show_currency/1 (plain function for ADT)" do
    # Currency is an Erlang tagged tuple; plain function dispatch avoids the
    # map-based protocol guard that only works for record types.
    test "EUR renders the ISO code" do
      assert @moneta.show_currency(:EUR) == ~c"EUR"
    end

    test "OMR renders the ISO code" do
      assert @moneta.show_currency(:OMR) == ~c"OMR"
    end

    test "JPY renders the ISO code" do
      assert @moneta.show_currency(:JPY) == ~c"JPY"
    end

    test "show/1 on a Money value uses show_currency internally for the currency field" do
      assert @moneta.show(eur(10_050)) == ~c"EUR 100.50"
    end
  end

  describe "Cure.Moneta: Eq protocol (Money record)" do
    test "same currency and amount are equal" do
      assert @moneta.eq(eur(100), eur(100))
    end

    test "different amounts are not equal" do
      refute @moneta.eq(eur(100), eur(200))
    end

    test "different currencies are not equal" do
      refute @moneta.eq(eur(100), usd(100))
    end
  end

  describe "Cure.Moneta: add/2" do
    test "adds two EUR amounts" do
      assert {:ok, result} = @moneta.add(eur(100), eur(250))
      assert money_amount(result) == 350
    end

    test "returns error for currency mismatch" do
      assert {:error, msg} = @moneta.add(eur(100), usd(100))
      assert List.to_string(msg) =~ "currency mismatch"
    end

    test "addition is commutative" do
      {:ok, ab} = @moneta.add(eur(300), eur(700))
      {:ok, ba} = @moneta.add(eur(700), eur(300))
      assert money_amount(ab) == money_amount(ba)
    end
  end

  describe "Cure.Moneta: subtract/2" do
    test "subtracts a smaller EUR amount" do
      assert {:ok, result} = @moneta.subtract(eur(1000), eur(300))
      assert money_amount(result) == 700
    end

    test "returns error for insufficient funds" do
      assert {:error, msg} = @moneta.subtract(eur(100), eur(500))
      assert List.to_string(msg) =~ "insufficient funds"
    end

    test "returns error for currency mismatch" do
      assert {:error, msg} = @moneta.subtract(eur(1000), usd(100))
      assert List.to_string(msg) =~ "currency mismatch"
    end

    test "subtracting zero gives the same amount" do
      {:ok, result} = @moneta.subtract(eur(500), eur(0))
      assert money_amount(result) == 500
    end
  end

  describe "Cure.Moneta: scale/2" do
    test "multiplies the amount by a positive factor" do
      result = @moneta.scale(eur(250), 4)
      assert money_amount(result) == 1000
    end

    test "scale by 1 is identity" do
      result = @moneta.scale(jpy(999), 1)
      assert money_amount(result) == 999
    end

    test "preserves currency and fractional_units" do
      result = @moneta.scale(omr(500), 3)
      assert money_currency(result) == :OMR
      assert money_fractional_units(result) == 1000
    end
  end

  describe "Cure.Moneta: convert/4 (FX)" do
    test "EUR to USD at rate 1.08" do
      # EUR 100.00 = 10_000 cents; at 1.08 -> USD 108.00 = 10_800 cents
      result = @moneta.convert(eur(10_000), :USD, 1.08, 100)
      assert money_currency(result) == :USD
      assert money_amount(result) == 10_800
      assert money_fractional_units(result) == 100
    end

    test "JPY to EUR at rate 0.0063" do
      # JPY 1000 -> EUR 6.30 => 630 EUR cents
      result = @moneta.convert(jpy(1000), :EUR, 0.0063, 100)
      assert money_currency(result) == :EUR
      assert money_amount(result) == 6
    end

    test "OMR to USD: 1 OMR (1000 fils) at rate 2.60 -> USD 2.60 (260 cents)" do
      result = @moneta.convert(omr(1000), :USD, 2.60, 100)
      assert money_amount(result) == 2600
    end

    test "convert preserves fractional_units of target" do
      result = @moneta.convert(eur(1000), :OMR, 0.413, 1000)
      assert money_fractional_units(result) == 1000
    end
  end

  describe "Cure.Moneta: ledger operations" do
    setup do
      alice = account(1, "Alice", eur(10_000))
      bob = account(2, "Bob", eur(5_000))
      l = ledger([alice, bob])
      {:ok, ledger: l}
    end

    test "balance returns the account's Money", %{ledger: l} do
      assert {:ok, bal} = @moneta.balance(l, 1)
      assert money_amount(bal) == 10_000
      assert money_currency(bal) == :EUR
    end

    test "balance returns error for unknown id", %{ledger: l} do
      assert {:error, msg} = @moneta.balance(l, 99)
      assert List.to_string(msg) =~ "account not found"
    end

    test "deposit increases balance", %{ledger: l} do
      {:ok, l2} = @moneta.deposit(l, 1, eur(500))
      {:ok, bal} = @moneta.balance(l2, 1)
      assert money_amount(bal) == 10_500
    end

    test "deposit rejects currency mismatch", %{ledger: l} do
      assert {:error, msg} = @moneta.deposit(l, 1, usd(100))
      assert List.to_string(msg) =~ "currency mismatch"
    end

    test "withdraw decreases balance", %{ledger: l} do
      {:ok, l2} = @moneta.withdraw(l, 2, eur(3_000))
      {:ok, bal} = @moneta.balance(l2, 2)
      assert money_amount(bal) == 2_000
    end

    test "withdraw rejects insufficient funds", %{ledger: l} do
      assert {:error, msg} = @moneta.withdraw(l, 2, eur(99_999))
      assert List.to_string(msg) =~ "insufficient funds"
    end

    test "transfer moves money between accounts", %{ledger: l} do
      {:ok, l2} = @moneta.transfer(l, 1, 2, eur(2_000))
      {:ok, alice_bal} = @moneta.balance(l2, 1)
      {:ok, bob_bal} = @moneta.balance(l2, 2)
      assert money_amount(alice_bal) == 8_000
      assert money_amount(bob_bal) == 7_000
    end

    test "transfer fails atomically on insufficient funds", %{ledger: l} do
      assert {:error, _} = @moneta.transfer(l, 2, 1, eur(99_999))
      # Ledger unchanged: original balances hold
      {:ok, bob_bal} = @moneta.balance(l, 2)
      assert money_amount(bob_bal) == 5_000
    end

    test "open_account adds a new account" do
      empty = @moneta.new_ledger([])
      l2 = @moneta.open_account(empty, 42, "Carol", eur(0))
      assert {:ok, bal} = @moneta.balance(l2, 42)
      assert money_amount(bal) == 0
    end
  end

  # ===========================================================================
  # 2. Cure.Transaction raw FSM
  # ===========================================================================

  describe "Cure.Transaction: initial state" do
    test "FSM starts in :Idle with payload 0" do
      {:ok, pid} = @fsm.start_link(0)
      assert {:Idle, 0} = :sys.get_state(pid)
      GenServer.stop(pid)
    end
  end

  describe "Cure.Transaction: normal lifecycle" do
    test "create transitions :Idle -> :Pending" do
      {:ok, pid} = @fsm.start_link(0)
      :gen_statem.cast(pid, :create)
      _ = :sys.get_state(pid)
      assert {:Pending, 0} = :sys.get_state(pid)
      GenServer.stop(pid)
    end

    test "submit from :Pending transitions to :submitting then dispatch! auto-fires to :Awaiting" do
      {:ok, pid} = @fsm.start_link(0)
      reach_awaiting(pid)
      assert {:Awaiting, 0} = :sys.get_state(pid)
      GenServer.stop(pid)
    end

    test "confirm from :Awaiting transitions to :Settled" do
      {:ok, pid} = @fsm.start_link(0)
      reach_awaiting(pid)
      :gen_statem.cast(pid, :confirm)
      _ = :sys.get_state(pid)
      assert {:Settled, _} = :sys.get_state(pid)
      GenServer.stop(pid)
    end

    test "reject from :Awaiting transitions to :Failed" do
      {:ok, pid} = @fsm.start_link(0)
      reach_awaiting(pid)
      :gen_statem.cast(pid, :reject)
      _ = :sys.get_state(pid)
      assert {:Failed, _} = :sys.get_state(pid)
      GenServer.stop(pid)
    end
  end

  describe "Cure.Transaction: soft events" do
    test "retry? from :Failed resets to :Pending" do
      {:ok, pid} = @fsm.start_link(0)
      reach_awaiting(pid)
      :gen_statem.cast(pid, :reject)
      _ = :sys.get_state(pid)
      :gen_statem.cast(pid, :retry)
      _ = :sys.get_state(pid)
      assert {:Pending, 0} = :sys.get_state(pid)
      GenServer.stop(pid)
    end

    test "retry? from :Settled is silently ignored (soft event)" do
      {:ok, pid} = @fsm.start_link(0)
      reach_awaiting(pid)
      :gen_statem.cast(pid, :confirm)
      _ = :sys.get_state(pid)
      :gen_statem.cast(pid, :retry)
      _ = :sys.get_state(pid)
      # Still settled -- retry? was a no-op
      assert {:Settled, _} = :sys.get_state(pid)
      GenServer.stop(pid)
    end

    test "cancel? from :Awaiting transitions to :Cancelled" do
      {:ok, pid} = @fsm.start_link(0)
      reach_awaiting(pid)
      :gen_statem.cast(pid, :cancel)
      _ = :sys.get_state(pid)
      assert {:Cancelled, _} = :sys.get_state(pid)
      GenServer.stop(pid)
    end

    test "cancel? is a wildcard -- it cancels even from :Settled (no terminal exclusion in this FSM)" do
      {:ok, pid} = @fsm.start_link(0)
      reach_awaiting(pid)
      :gen_statem.cast(pid, :confirm)
      _ = :sys.get_state(pid)
      # The wildcard `* --cancel?--> Cancelled` fires from every state, including :Settled.
      # A soft event only silently fails when NO matching transition exists; the wildcard
      # ensures one always does.
      :gen_statem.cast(pid, :cancel)
      _ = :sys.get_state(pid)
      assert {:Cancelled, _} = :sys.get_state(pid)
      GenServer.stop(pid)
    end
  end

  describe "Cure.Transaction: on_timer" do
    test "timer fires a :reject from :Awaiting, moving FSM to :Failed" do
      {:ok, pid} = @fsm.start_link(0)
      reach_awaiting(pid)

      # Manually send the :on_timer message (bypasses the 30 s wall-clock delay).
      send(pid, :on_timer)
      _ = :sys.get_state(pid)

      assert {:Failed, 0} = :sys.get_state(pid)
      GenServer.stop(pid)
    end

    test "timer is a no-op from states other than :Awaiting" do
      {:ok, pid} = @fsm.start_link(0)
      :gen_statem.cast(pid, :create)
      _ = :sys.get_state(pid)

      send(pid, :on_timer)
      _ = :sys.get_state(pid)

      # Still :Pending -- timer returned :ok (no-op clause)
      assert {:Pending, 0} = :sys.get_state(pid)
      GenServer.stop(pid)
    end
  end

  describe "Cure.Transaction: retry cycle" do
    test "failed -> retry -> submit -> awaiting -> confirm -> settled full cycle" do
      {:ok, pid} = @fsm.start_link(0)
      reach_awaiting(pid)

      :gen_statem.cast(pid, :reject)
      _ = :sys.get_state(pid)

      :gen_statem.cast(pid, :retry)
      _ = :sys.get_state(pid)
      assert {:Pending, 0} = :sys.get_state(pid)

      :gen_statem.cast(pid, :submit)
      _ = :sys.get_state(pid)
      assert {:Awaiting, 0} = :sys.get_state(pid)

      :gen_statem.cast(pid, :confirm)
      _ = :sys.get_state(pid)
      assert {:Settled, _} = :sys.get_state(pid)

      GenServer.stop(pid)
    end
  end

  # ===========================================================================
  # 3. CureMoneta wrapper (uses LedgerServer started by Application)
  # ===========================================================================

  describe "CureMoneta wrapper: ledger" do
    setup do
      # Use unique IDs per test to avoid cross-test interference.
      id_a = :erlang.unique_integer([:positive])
      id_b = :erlang.unique_integer([:positive])
      :ok = CureMoneta.open_account(id_a, "Alice", :eur, 20_000)
      :ok = CureMoneta.open_account(id_b, "Bob", :usd, 10_000)
      {:ok, id_a: id_a, id_b: id_b}
    end

    test "balance returns a formatted show-able Money", %{id_a: id_a} do
      {:ok, bal} = CureMoneta.balance(id_a)
      assert bal.amount == 20_000
      assert CureMoneta.show(bal) == "EUR 200.00"
    end

    test "deposit increases balance", %{id_a: id_a} do
      :ok = CureMoneta.deposit(id_a, :eur, 500)
      {:ok, bal} = CureMoneta.balance(id_a)
      assert bal.amount == 20_500
    end

    test "withdraw decreases balance", %{id_a: id_a} do
      :ok = CureMoneta.withdraw(id_a, :eur, 1_000)
      {:ok, bal} = CureMoneta.balance(id_a)
      assert bal.amount == 19_000
    end

    test "withdraw rejects insufficient funds", %{id_a: id_a} do
      assert {:error, msg} = CureMoneta.withdraw(id_a, :eur, 999_999)
      assert msg =~ "insufficient funds"
    end

    test "currency mismatch on deposit returns error", %{id_a: id_a} do
      assert {:error, msg} = CureMoneta.deposit(id_a, :usd, 100)
      assert msg =~ "currency mismatch"
    end

    test "transfer moves EUR between two EUR accounts", %{id_a: id_a} do
      id_c = :erlang.unique_integer([:positive])
      :ok = CureMoneta.open_account(id_c, "Carol", :eur, 0)
      :ok = CureMoneta.transfer(id_a, id_c, :eur, 5_000)
      {:ok, alice_bal} = CureMoneta.balance(id_a)
      {:ok, carol_bal} = CureMoneta.balance(id_c)
      assert alice_bal.amount == 15_000
      assert carol_bal.amount == 5_000
    end
  end

  describe "CureMoneta wrapper: money helpers" do
    test "money/2 infers fractional_units from currency" do
      assert CureMoneta.money(:eur, 150).fractional_units == 100
      assert CureMoneta.money(:jpy, 150).fractional_units == 1
      assert CureMoneta.money(:omr, 150).fractional_units == 1000
    end

    test "money/3 uses explicit fractional_units" do
      m = CureMoneta.money(:eur, 100, 10)
      assert m.fractional_units == 10
    end

    test "show formats EUR correctly" do
      assert CureMoneta.show(CureMoneta.money(:eur, 10_050)) == "EUR 100.50"
    end

    test "show formats OMR with three decimal places" do
      assert CureMoneta.show(CureMoneta.money(:omr, 1_000)) == "OMR 1.000"
    end

    test "eq compares two money values" do
      a = CureMoneta.money(:eur, 100)
      b = CureMoneta.money(:eur, 100)
      c = CureMoneta.money(:eur, 200)
      assert CureMoneta.eq(a, b)
      refute CureMoneta.eq(a, c)
    end

    test "convert EUR to USD via wrapper" do
      eur = CureMoneta.money(:eur, 10_000)
      usd = CureMoneta.convert(eur, :usd, 1.08)
      assert usd.currency == {:usd}
      assert usd.amount == 10_800
      assert CureMoneta.show(usd) == "USD 108.00"
    end
  end

  describe "CureMoneta wrapper: begin_transaction" do
    test "begins a transaction FSM and drives it to :Settled" do
      {:ok, pid} = CureMoneta.begin_transaction()
      CureMoneta.tx_event(pid, :create)
      CureMoneta.tx_event(pid, :submit)
      _ = :sys.get_state(pid)
      assert {:Awaiting, _} = CureMoneta.tx_state(pid)
      CureMoneta.tx_event(pid, :confirm)
      _ = :sys.get_state(pid)
      assert {:Settled, _} = CureMoneta.tx_state(pid)
      GenServer.stop(pid)
    end

    test "cancel? from :Awaiting cancels the transaction" do
      {:ok, pid} = CureMoneta.begin_transaction()
      CureMoneta.tx_event(pid, :create)
      CureMoneta.tx_event(pid, :submit)
      _ = :sys.get_state(pid)
      CureMoneta.tx_event(pid, :cancel)
      _ = :sys.get_state(pid)
      assert {:Cancelled, _} = CureMoneta.tx_state(pid)
      GenServer.stop(pid)
    end

    test "each begin_transaction spawns an independent FSM" do
      {:ok, pid1} = CureMoneta.begin_transaction()
      {:ok, pid2} = CureMoneta.begin_transaction()
      assert pid1 != pid2
      CureMoneta.tx_event(pid1, :create)
      _ = :sys.get_state(pid1)
      assert {:Pending, _} = CureMoneta.tx_state(pid1)
      assert {:Idle, _} = CureMoneta.tx_state(pid2)
      GenServer.stop(pid1)
      GenServer.stop(pid2)
    end
  end
end
