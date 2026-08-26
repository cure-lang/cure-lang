defmodule Cure.Stdlib.OtpRawPinTest do
  @moduledoc """
  The concrete `no_widening_narrow` validator (parent spec §12).

  Every op in `Std.Otp.Raw` is an `@extern` over a stock BEAM BIF, and the parent spec
  (§3.1) requires each to carry its most permissive HONEST type. That cannot be checked
  automatically — it would need an oracle for every BIF's return type — so this pins the
  table the executed conformance audit established by probing each BIF's real return value
  (https://github.com/cure-lang/cure-otp/tree/main/docs/research/process-types/raw-algebra-conformance-checklist.md, §4 F-4).

  A change here is not a test to update. It is a claim about what the BEAM returns, and it
  needs the evidence the audit produced: run the BIF and look.
  """
  use ExUnit.Case, async: true

  @source "lib/std/otp_raw.cure"

  # raw op => the exact return type its declaration must carry.
  @pinned %{
    "raw_term_is_atom" => "Bool",
    "raw_term_is_pid" => "Bool",
    "raw_term_is_tuple" => "Bool",
    "raw_term_is_integer" => "Bool",
    "raw_term_is_float" => "Bool",
    "raw_term_is_boolean" => "Bool",
    "raw_term_is_binary" => "Bool",
    "raw_term_tuple_size" => "Int",
    "raw_term_tuple_element" => "RawTerm",
    "raw_term_atom" => "Atom",
    "raw_term_pid" => "BarePid",
    "raw_term_integer" => "Int",
    "raw_term_float" => "Float",
    "raw_term_boolean" => "Bool",
    "raw_term_binary" => "Binary",
    "raw_actor_server" => "RawServerPid(m, q, r)",
    "raw_fsm_pid" => "RawFsmPid(event, state, data)",
    "raw_supervisor_pid" => "RawSupervisorPid",
    "raw_dep_actor_server" => "RawDepServerPid(m, q, rep)",
    "raw_dep_actor_base" => "RawServerPid(m, q, Unit)",
    "raw_self" => "Effect(RawPid(m, m, Plain))",
    "raw_spawn" => "Effect(RawPid(m, m, Plain))",
    "raw_spawn_link" => "Effect(RawPid(m, m, Plain))",
    "raw_send" => "Effect(m)",
    "raw_cast" => "Effect(Atom)",
    "raw_stop" => "Effect(Atom)",
    # `:gen.reply/2` returns the atom `:ok` after delivering the reply.
    "raw_reply" => "Effect(Atom)",
    "raw_call" => "Effect(r)",
    "raw_call_dep" => "Effect(res)",
    "raw_subject_new" => "Effect(Tuple(RawPid(m, m, Plain), Ref))",
    "raw_subject_send" => "Effect(Atom)",
    "raw_subject_receive" => "Effect(Option(m))",
    "raw_selector_new" => "Selector(p)",
    "raw_selector_select_map" => "Selector(p)",
    "raw_selector_receive" => "Effect(Option(p))",
    "raw_name_register" => "Effect(Bool)",
    "raw_name_whereis" => "Effect(Option(RawPid(m, m, Plain)))",
    "raw_name_unregister" => "Effect(Bool)",
    "raw_link" => "Effect(Bool)",
    "raw_unlink" => "Effect(Bool)",
    "raw_exit" => "Effect(Bool)",
    "raw_register" => "Effect(Bool)",
    "raw_unregister" => "Effect(Bool)",
    "raw_demonitor" => "Effect(Bool)",
    "raw_demonitor_flush" => "Effect(Bool)",
    "raw_is_alive" => "Effect(Bool)",
    "raw_monitor" => "Effect(MonitorRef)",
    "raw_send_after" => "Effect(TimerRef)",
    "raw_cancel_timer" => "Effect(Int | Bool)",
    "raw_whereis" => "Effect(BarePid | :undefined)",
    "raw_start_link" => "Effect(Tuple)",
    "raw_start_link_unnamed" => "Effect(Tuple)",
    "raw_start_link_term" => "Effect(RawTerm)",
    "raw_statem_start_link" => "Effect(Tuple)",
    "raw_statem_start_link_unnamed" => "Effect(Tuple)",
    "raw_statem_start_link_term" => "Effect(RawTerm)",
    "raw_statem_cast" => "Effect(Atom)",
    "raw_supervisor_start_link" => "Effect(Tuple)",
    "raw_supervisor_start_link_term" => "Effect(RawTerm)",
    "raw_supervisor_stop" => "Effect(Atom)",
    "raw_server_cast" => "Effect(Atom)",
    "raw_server_call" => "Effect(r)",
    "raw_server_call_dep" => "Effect(res)",
    "raw_server_stop" => "Effect(Atom)",
    "raw_term" => "RawTerm"
  }

  defp declarations do
    @source
    |> File.read!()
    |> String.split("\n")
    |> Enum.filter(&(&1 =~ ~r/^\s*fn raw_\w+\(/))
    |> Map.new(fn line ->
      [_, name] = Regex.run(~r/fn (raw_\w+)\(/, line)
      {name, line}
    end)
  end

  test "every raw op is pinned, and every pinned op still exists" do
    declared = declarations() |> Map.keys() |> MapSet.new()
    pinned = @pinned |> Map.keys() |> MapSet.new()

    assert MapSet.difference(pinned, declared) |> Enum.empty?(),
           "pinned ops that no longer exist: #{inspect(MapSet.difference(pinned, declared))}"

    assert MapSet.difference(declared, pinned) |> Enum.empty?(),
           "raw ops with no pinned return type — add them to @pinned WITH evidence from " <>
             "the BIF's actual return value: #{inspect(MapSet.difference(declared, pinned))}"
  end

  test "each raw op declares exactly its audited return type" do
    decls = declarations()

    for {op, expected} <- @pinned do
      line = Map.fetch!(decls, op)

      assert String.contains?(line, "-> " <> expected),
             "#{op} no longer returns #{expected}.\n  declared: #{String.trim(line)}\n" <>
               "  This is a claim about what the BEAM returns. Re-probe the BIF before repinning."
    end
  end

  test "no raw op declares Effect(Unit) — none of these BIFs returns unit" do
    for {op, line} <- declarations() do
      refute String.contains?(line, "-> Effect(Unit)"),
             "#{op} declares Effect(Unit). Ten ops did, and emit.ex does no result " <>
               "coercion, so the BIF's real return value was inhabiting Unit. See the audit, F-4."
    end
  end
end
