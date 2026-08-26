defmodule Cure.Stdlib.OtpRawTest do
  @moduledoc """
  `Std.Otp.Raw` — the sealed effect-typed raw base of the BEAM process algebra —
  elaborates on the DEPENDENT pipeline, and every side-effecting operation returns
  `Effect(T)` (no purity lie). This is the first real consumer of the whole Effect
  stack (surface `Effect(T)` + effectful `@extern` + graded binders) composing into
  a library. Message/reply payloads are POLYMORPHIC (the narrow point where the
  typed `Std.Otp` supplies a message code), not `Any`.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Elab.Program
  alias Cure.Core.Env

  setup_all do
    src = File.read!("lib/std/otp_raw.cure")
    {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, env, locals} = Program.check_ast_with_locals(ast)
    {:ok, env: env, locals: locals}
  end

  # Walk a def's Pi telescope to its result and check the head is `Effect(_)`.
  defp effect_result?({:pi, _g, _d, cod}), do: effect_result?(cod)
  defp effect_result?({:effect_type, _}), do: true
  defp effect_result?(_), do: false

  test "the module elaborates on the dependent pipeline", %{locals: locals} do
    local_bases = MapSet.new(locals, &Cure.Elab.Name.base/1)

    assert "raw_self" in local_bases
    assert "raw_spawn" in local_bases
    assert "raw_spawn_link" in local_bases
    assert "raw_start_link" in local_bases
    assert "raw_start_link_unnamed" in local_bases
    assert "raw_statem_start_link" in local_bases
    assert "raw_statem_start_link_unnamed" in local_bases
    assert "raw_supervisor_start_link" in local_bases
    assert "raw_send" in local_bases
    assert "raw_call" in local_bases
  end

  # The `Plain` tag is `RawPid`'s third argument: the process the VM hands us speaks no
  # gen_server protocol. It is a phantom at kind `Type` — a `{:data, :Plain, [], []}` in
  # the TYPE, and nothing at all at runtime.
  test "raw_self binds its erased message index before returning Effect(RawPid(m, m, Plain))",
       %{env: env} do
    assert {:pi, :erased, {:type, 0},
            {:effect_type,
             {:data, :"Std.Otp.Raw#RawPid", [{:var, 0}, {:var, 0}, {:data, :"Std.Otp.Raw#Plain", [], []}], []}}} =
             Env.get_def(env, :raw_self).type
  end

  test "every side-effecting op returns Effect(_) — the purity lie is closed", %{env: env} do
    for name <- [
          :raw_send,
          :raw_spawn,
          :raw_spawn_link,
          :raw_start_link,
          :raw_start_link_unnamed,
          :raw_statem_start_link,
          :raw_statem_start_link_unnamed,
          :raw_supervisor_start_link,
          :raw_cast,
          :raw_call,
          :raw_monitor,
          :raw_stop,
          :raw_send_after,
          :raw_cancel_timer,
          :raw_demonitor,
          :raw_link,
          :raw_unlink,
          :raw_exit,
          :raw_is_alive,
          :raw_register,
          :raw_unregister,
          :raw_whereis
        ] do
      assert effect_result?(Env.get_def(env, name).type),
             "#{name} must return Effect(_), got #{inspect(Env.get_def(env, name).type)}"
    end
  end

  test "raw_send is a postulated FFI global (an @extern), not an inlinable def", %{env: env} do
    assert {:extern, {:erlang, :send, 2}} = Env.get_def(env, :raw_send).body
  end

  test "messages are polymorphic (not Any): raw_send binds a Type param for the message", %{
    env: env
  } do
    # {m : Type(erased)} -> Pid -> m -> Effect(Unit): the outer binder is the
    # erased message-type param, and the message argument is that bound variable.
    assert {:pi, :erased, {:type, 0}, _} = Env.get_def(env, :raw_send).type
  end
end
