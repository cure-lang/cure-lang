defmodule Cure.Audit.ShimConformance do
  @moduledoc """
  Phase 1 of the axiom-surface program: mechanically check the `CURE RUNTIME`
  axioms against the Elixir that implements them.

  A bodyless `@extern` is a typed FFI postulate — the signature IS the type, and
  nothing checks it. This harness executes each postulated function on generated
  arguments and asks four questions:

    * **referential transparency** — `f(args) == f(args)`
    * **no hidden state** — the process dictionary, the mailbox and the ETS table
      set are untouched
    * **type conformance** — the result matches the declared return type's
      runtime shape
    * **totality** — no raise, no exit, no throw

  It is a **transitional safety net**. The shims exist only until Phases 2 and 3
  rewrite them in Cure or rebase them onto OTP; when the last `:cure_std_*`
  module is gone, this module goes with it.

  ## Two things it cannot do

  `Std.Http`'s four axioms perform network I/O. Executing them in a test suite is
  not acceptable and mocking `:httpc` would test the mock, so they are excluded
  and classified `:effectful` by inspection. The harness reports how many axioms
  it executed so the checked and excluded totals remain explicit.

  Passing on generated arguments is evidence, not proof. It is strictly more than
  the zero evidence available today, and a rewrite in Cure is what turns evidence
  into proof.

  ## Shapes are the DEPENDENT erasure

  The classic pipeline is being removed. The shims now emit the dependent
  pipeline's constructor erasure, and this harness checks against it:

    * `C(a, b)` → `{:C, a, b}`; a nullary `C()` → the bare atom `:C`
    * `rec R` → `{:R, field1, …}` in declaration order

  So `Ok(v)` is `{:ok, v}`, `None()` is `:none`, `Null()` is `:Null`, and
  `rec Matched(whole, groups)` is `{:Matched, whole, groups}`. The erasure rule
  was measured directly (`Std.Result`/`Std.Option` elaborate; a standalone ADT
  and record confirmed the nullary-atom and tuple-in-declaration-order rules).
  These modules do not yet dependent-elaborate (#23), so end-to-end consumption
  through the dependent pipeline cannot be exercised here; this harness checks
  the runtime shapes against the measured rule. See
  `pipeline-ctor-erasure-divergence`.
  """

  alias Antigen.Backend.StreamData, as: Backend

  @seed 20_260_711
  @samples 20

  # Referential transparency is checked on fewer samples, because detecting a
  # clock requires letting time pass between the two calls. Two back-to-back
  # reads of `:erlang.system_time(:microsecond)` can land in the same
  # microsecond, and `time.now` then looks pure. A pure function is unaffected
  # by the delay; an impure one is exactly what the delay exposes.
  @rt_samples 3
  @rt_delay_ms 2

  # ---------------------------------------------------------------------------
  # Generator descriptors (Antigen's backend-agnostic descriptor language).
  # `StreamData` is named in exactly one module, and this is not it.
  # ---------------------------------------------------------------------------

  defp ret(x), do: {:return, x}
  defp map(g, f), do: {:bind, g, fn v -> ret(f.(v)) end}

  defp seq([]), do: ret([])

  defp seq([g | rest]),
    do: {:bind, g, fn v -> {:bind, seq(rest), fn vs -> ret([v | vs]) end} end}

  defp int, do: {:member_of, Enum.to_list(-30..30)}
  defp nonneg, do: {:member_of, Enum.to_list(0..30)}
  defp node_atom, do: {:member_of, [:n1, :n2, :n3]}
  defp stamp, do: {:member_of, Enum.to_list(1..20)}

  # `t` is instantiated at Int everywhere, so type conformance is checkable.
  defp elem, do: int()

  defp int_list, do: {:member_of, [[], [1], [3, 1, 2], [5, 5], [-1, 0, 1]]}
  # -- CRDT states, built from the module's own constructors -------------------

  defp gcounter do
    map(seq([node_atom(), nonneg(), node_atom(), nonneg()]), fn [n1, b1, n2, b2] ->
      :cure_std_crdt.g_empty()
      |> :cure_std_crdt.g_increment(n1, b1)
      |> :cure_std_crdt.g_increment(n2, b2)
    end)
  end

  defp pncounter do
    map(seq([node_atom(), nonneg(), node_atom(), nonneg()]), fn [n1, b1, n2, b2] ->
      :cure_std_crdt.pn_empty()
      |> :cure_std_crdt.pn_increment(n1, b1)
      |> :cure_std_crdt.pn_decrement(n2, b2)
    end)
  end

  defp orset do
    map(seq([node_atom(), elem(), elem()]), fn [n, e1, e2] ->
      :cure_std_crdt.or_empty()
      |> :cure_std_crdt.or_add(n, 1, e1)
      |> :cure_std_crdt.or_add(n, 2, e2)
    end)
  end

  # An empty register is a legitimate LWWRegister, so it must be generated.
  defp lww do
    {:one_of,
     [
       map(node_atom(), &:cure_std_crdt.lww_empty/1),
       map(seq([node_atom(), elem(), stamp()]), fn [n, v, s] ->
         :cure_std_crdt.lww_set(:cure_std_crdt.lww_empty(n), v, s, n)
       end)
     ]}
  end

  defp mv do
    {:one_of,
     [
       ret(:cure_std_crdt.mv_empty()),
       map(seq([node_atom(), elem(), stamp()]), fn [n, v, s] ->
         :cure_std_crdt.mv_write(:cure_std_crdt.mv_empty(), v, s, n)
       end)
     ]}
  end

  defp instant, do: map(int(), fn n -> :cure_std_time.of_unix(1_700_000_000 + n) end)

  # The erased form of a Cure `String`; see the `:cure_string` shape below.
  defp cure_string(text), do: {:String, String.to_charlist(text)}

  defp duration do
    map(seq([int(), int()]), fn [a, b] ->
      :cure_std_time.diff(:cure_std_time.of_unix(a), :cure_std_time.of_unix(b))
    end)
  end

  # A deterministic generator + property pair for `forall_shrunk`.
  defp gen_fn, do: {:member_of, [fn _ -> 7 end, fn _ -> 100 end]}
  defp prop_fn, do: {:member_of, [fn _ -> true end, fn n -> n < 50 end]}

  # ---------------------------------------------------------------------------
  # The axiom table. 34 executable axioms; `cure_std_http`'s 4 are excluded.
  # ---------------------------------------------------------------------------

  @doc "Every `CURE RUNTIME` axiom this harness executes."
  def axioms do
    crdt() ++ time() ++ gen() ++ test_axioms()
  end

  @doc """
  Axioms excluded from execution, with the reason. These are the real target
  MFAs (the `@extern` targets), not the Cure surface names — `Std.Http`'s
  `get_with_headers/2` targets `:cure_std_http.get/2`, so the tuple names `get`.
  """
  def excluded do
    [
      {{:cure_std_http, :get, 1}, "network I/O"},
      {{:cure_std_http, :get, 2}, "network I/O"},
      {{:cure_std_http, :post, 3}, "network I/O"},
      {{:cure_std_http, :head, 1}, "network I/O"}
    ]
  end

  defp a(mfa, args, shape, expect \\ :pure),
    do: %{mfa: mfa, args: args, shape: shape, expect: expect}

  defp crdt do
    gc = {:struct, :g_counter}
    pc = {:struct, :pn_counter}
    os = {:struct, :or_set}
    lw = {:struct, :lww_register}
    mvr = {:struct, :mv_register}

    [
      a({:cure_std_crdt, :g_empty, 0}, ret([]), gc),
      a({:cure_std_crdt, :g_increment, 3}, seq([gcounter(), node_atom(), nonneg()]), gc),
      a({:cure_std_crdt, :g_value, 1}, seq([gcounter()]), :int),
      a({:cure_std_crdt, :g_merge, 2}, seq([gcounter(), gcounter()]), gc),
      a({:cure_std_crdt, :pn_empty, 0}, ret([]), pc),
      a({:cure_std_crdt, :pn_increment, 3}, seq([pncounter(), node_atom(), nonneg()]), pc),
      a({:cure_std_crdt, :pn_decrement, 3}, seq([pncounter(), node_atom(), nonneg()]), pc),
      a({:cure_std_crdt, :pn_value, 1}, seq([pncounter()]), :int),
      a({:cure_std_crdt, :pn_merge, 2}, seq([pncounter(), pncounter()]), pc),
      a({:cure_std_crdt, :or_empty, 0}, ret([]), os),
      a({:cure_std_crdt, :or_add, 4}, seq([orset(), node_atom(), stamp(), elem()]), os),
      a({:cure_std_crdt, :or_remove, 2}, seq([orset(), elem()]), os),
      a({:cure_std_crdt, :or_value, 1}, seq([orset()]), {:list, :int}),
      a({:cure_std_crdt, :or_merge, 2}, seq([orset(), orset()]), os),
      a({:cure_std_crdt, :lww_empty, 1}, seq([node_atom()]), lw),
      a({:cure_std_crdt, :lww_set, 4}, seq([lww(), elem(), stamp(), node_atom()]), lw),
      a({:cure_std_crdt, :lww_value, 1}, seq([lww()]), {:option, :int}),
      a({:cure_std_crdt, :lww_merge, 2}, seq([lww(), lww()]), lw),
      a({:cure_std_crdt, :mv_empty, 0}, ret([]), mvr),
      a({:cure_std_crdt, :mv_write, 4}, seq([mv(), elem(), stamp(), node_atom()]), mvr),
      a({:cure_std_crdt, :mv_values, 1}, seq([mv()]), {:list, :int}),
      a({:cure_std_crdt, :mv_merge, 2}, seq([mv(), mv()]), mvr)
    ]
  end

  defp time do
    inst = {:struct, :instant}
    # Duration is surface-constructible, so it erases to `{:Duration, micros}`.
    dur = :duration
    # A mix of valid and invalid ISO-8601 strings, so BOTH the `{:Ok, Instant}`
    # and the `{:Error, ParseError}` branches of parse_iso8601 are shape-checked.
    # `String` erases to `{:String, code_points}`, which is what these externs
    # actually receive from Cure — a bare binary is not a Cure `String`.
    iso =
      {:member_of, Enum.map(["2026-05-01T09:00:00Z", "2026-04-21T15:11:46.5Z", "not-a-date", ""], &cure_string/1)}

    [
      # Reads the clock. Declared `-> Instant ! Io`, but `declarations.ex` never
      # reads an effect, so the postulate is pure. It is not.
      a({:cure_std_time, :now, 0}, ret([]), inst, :effectful),
      a({:cure_std_time, :utc_now, 0}, ret([]), inst, :effectful),
      a({:cure_std_time, :parse_iso8601, 1}, seq([iso]), {:result, inst, :parse_error}),
      a({:cure_std_time, :format_iso8601, 1}, seq([instant()]), :cure_string),
      a({:cure_std_time, :add, 2}, seq([instant(), duration()]), inst),
      a({:cure_std_time, :diff, 2}, seq([instant(), instant()]), dur),
      a(
        {:cure_std_time, :zone, 2},
        seq([instant(), {:member_of, Enum.map(["UTC", "+01:00", "Bad/Zone"], &cure_string/1)}]),
        {:result, :cure_string, :parse_error}
      ),
      a({:cure_std_time, :to_unix, 1}, seq([instant()]), :int),
      a({:cure_std_time, :of_unix, 1}, seq([int()]), inst)
    ]
  end

  defp gen do
    [
      a({:cure_std_gen, :shrink_int, 1}, seq([int()]), {:list, :int}),
      a({:cure_std_gen, :shrink_list, 1}, seq([int_list()]), {:list, {:list, :int}})
    ]
  end

  defp test_axioms do
    [
      a(
        {:cure_std_test, :forall_shrunk, 3},
        seq([gen_fn(), prop_fn(), {:member_of, [0, 3, 5]}]),
        {:result, :atom, :int}
      )
    ]
  end

  # ---------------------------------------------------------------------------
  # The four properties
  # ---------------------------------------------------------------------------

  @doc """
  Run one axiom over generated arguments. Returns a map of property => :ok or
  {:failed, detail}.
  """
  def check(axiom, samples \\ @samples) do
    arg_sets = Backend.sample_seeded(axiom.args, samples, @seed)

    acc =
      Enum.reduce(arg_sets, %{}, fn args, acc ->
        acc
        |> merge_prop(:no_hidden_state, no_hidden_state(axiom.mfa, args))
        |> merge_prop(:totality, totality(axiom.mfa, args))
        |> merge_prop(:type_conformance, type_conformance(axiom.mfa, args, axiom.shape))
      end)

    Enum.reduce(Enum.take(arg_sets, @rt_samples), acc, fn args, acc ->
      merge_prop(acc, :referential_transparency, referentially_transparent(axiom.mfa, args))
    end)
  end

  # First failure per property wins; :ok only if every sample passed.
  defp merge_prop(acc, key, result) do
    case Map.get(acc, key, :ok) do
      :ok -> Map.put(acc, key, result)
      already_failed -> Map.put(acc, key, already_failed)
    end
  end

  defp referentially_transparent({m, f, _}, args) do
    first = invoke(m, f, args)
    # Let the clock move. A pure function does not notice.
    Process.sleep(@rt_delay_ms)
    second = invoke(m, f, args)

    case {first, second} do
      {{:ok, a}, {:ok, b}} when a == b -> :ok
      {{:ok, a}, {:ok, b}} -> {:failed, "#{inspect(a)} != #{inspect(b)}"}
      # A raise is reported by the totality property, not this one.
      _ -> :ok
    end
  end

  defp no_hidden_state({m, f, args_len} = _mfa, args) do
    task =
      Task.async(fn ->
        # ETS tables are scoped to THIS process's ownership, not a VM-global
        # `:ets.all()` count — that global count races against any concurrent
        # async test creating a table. A shim that opens a table owns it here.
        before_tables = owned_tables(self())
        before_dict = Process.get()
        _ = invoke(m, f, args)
        after_dict = Process.get()
        after_tables = owned_tables(self())

        {:message_queue_len, mailbox} = Process.info(self(), :message_queue_len)

        cond do
          after_dict != before_dict ->
            {:failed, "process dictionary written: #{inspect(after_dict -- before_dict)}"}

          mailbox != 0 ->
            {:failed, "#{mailbox} message(s) in mailbox"}

          after_tables != before_tables ->
            {:failed, "created an ETS table"}

          true ->
            :ok
        end
      end)

    _ = args_len
    Task.await(task, 5_000)
  end

  # Blind spot, accepted: a call that creates AND deletes a table within itself
  # leaves the before/after owned set identical. No shim touches ETS at all
  # (grep `:ets` in lib/cure/stdlib/*.ex is empty), so this cannot mask a live
  # finding today; a shim that used ETS transiently would need a heavier probe.
  defp owned_tables(pid) do
    :ets.all()
    |> Enum.filter(fn t ->
      # A table can vanish between `all/0` and `info/2`; treat that as not-owned.
      :ets.info(t, :owner) == pid
    end)
    |> MapSet.new()
  end

  defp totality({m, f, _}, args) do
    case invoke(m, f, args) do
      {:ok, _} -> :ok
      {:raised, e} -> {:failed, "raised #{inspect(e)}"}
    end
  end

  defp type_conformance({m, f, _}, args, shape) do
    case invoke(m, f, args) do
      {:ok, v} ->
        if shape?(shape, v),
          do: :ok,
          else: {:failed, "#{inspect(v)} is not #{inspect(shape)}"}

      # Totality reports the raise; do not double-count it here.
      {:raised, _} ->
        :ok
    end
  end

  defp invoke(m, f, args) do
    {:ok, apply(m, f, args)}
  rescue
    e -> {:raised, e}
  catch
    kind, reason -> {:raised, {kind, reason}}
  end

  # ---------------------------------------------------------------------------
  # Runtime shapes. These are the DEPENDENT erasure: constructor-name tags,
  # nullary -> bare atom, records -> tuples in declaration order.
  # ---------------------------------------------------------------------------

  defp shape?(:any, _v), do: true
  defp shape?(:int, v), do: is_integer(v)
  defp shape?(:atom, v), do: is_atom(v)
  defp shape?(:bool, v), do: is_boolean(v)
  defp shape?(:binary, v), do: is_binary(v)
  defp shape?({:struct, tag}, v), do: is_map(v) and Map.get(v, :__struct__) == tag
  defp shape?({:list, s}, v), do: is_list(v) and Enum.all?(v, &shape?(s, &1))
  defp shape?({:result, ok, _err}, {:ok, v}), do: shape?(ok, v)
  defp shape?({:result, _ok, err}, {:error, e}), do: shape?(err, e)
  defp shape?({:result, _, _}, _), do: false

  # OTP-compatible dependent erasure: `Some(v)` → `{:some, v}`; `None()` → `:none`.
  defp shape?({:option, _s}, :none), do: true
  defp shape?({:option, s}, {:some, v}), do: shape?(s, v)
  defp shape?({:option, _}, _), do: false

  # `rec Matched(whole, groups)` → `{:Matched, whole, groups}`; every captured
  # group is itself a String.
  defp shape?(:matched, {:Matched, whole, groups}),
    do: is_binary(whole) and is_list(groups) and Enum.all?(groups, &is_binary/1)

  defp shape?(:matched, _), do: false

  # `rec Duration(micros)` → `{:Duration, micros}`.
  defp shape?(:duration, {:Duration, m}), do: is_integer(m)
  defp shape?(:duration, _), do: false

  # `rec String { characters: List(Char) }` → `{:String, code_points}`. A Cure
  # `String` is NOT a binary and not a bare charlist: an `@extern` is a direct
  # remote call with no marshalling, so a shim declared over `String` has to
  # produce and accept exactly this pair.
  defp shape?(:cure_string, {:String, chars}), do: is_list(chars) and Enum.all?(chars, &is_integer/1)
  defp shape?(:cure_string, _), do: false

  # `ParseError = InvalidFormat(String) | OutOfRange(String)` — so the Error side
  # of a Result is really checked, not waved through with `:any`.
  defp shape?(:parse_error, {:InvalidFormat, m}), do: shape?(:cure_string, m)
  defp shape?(:parse_error, {:OutOfRange, m}), do: shape?(:cure_string, m)
  defp shape?(:parse_error, _), do: false

  defp shape?(:json, v) do
    v == :Null or match?({:Bool, _}, v) or match?({:Num, _}, v) or
      match?({:Str, _}, v) or match?({:Arr, _}, v) or match?({:Obj, _}, v)
  end

  # ---------------------------------------------------------------------------
  # The partition — the real output (spec §5.3)
  # ---------------------------------------------------------------------------

  @doc """
  Classify every executed axiom.

    * `:conformant`  — all four properties held on every sample
    * `:effectful`   — impure by nature; cannot be repaired without the `Effect`
                        former (`time.now`, `time.utc_now`, and `http.*`)
    * `:type_defect` — the implementation does not inhabit the declared type;
                        repairable by changing the Cure signature
  """
  def classify do
    Map.new(axioms(), fn axiom ->
      results = check(axiom)
      failures = for {prop, {:failed, why}} <- results, do: {prop, why}
      {axiom.mfa, {verdict(axiom.expect, failures), failures}}
    end)
  end

  defp verdict(:pure, []), do: :conformant
  defp verdict(:pure, _failures), do: :unexpected_failure
  defp verdict(:effectful, []), do: :unexpectedly_pure
  defp verdict(:effectful, _), do: :effectful
  defp verdict(:type_defect, []), do: :unexpectedly_conformant
  defp verdict(:type_defect, _), do: :type_defect
end
