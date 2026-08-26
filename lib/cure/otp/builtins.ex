defmodule Cure.Otp.Builtins do
  @moduledoc """
  Runtime FFI helpers for `Std.Otp`'s `Subject` abstraction — a typed message
  address `{owner_pid, tag_ref}` in the style of Gleam's `Subject(message)`.

  A `Subject` is a `{pid, reference}` pair: the owning process plus a fresh,
  unique tag. `subject_send` delivers `{tag, message}` to the owner's mailbox;
  `subject_receive` does a tagged selective receive, so one process can own
  several subjects of different message types and receive each independently.
  These are the operations that cannot be expressed as plain BIFs (the tagged
  `receive ... after ... end` needs Erlang receive syntax); `Std.Otp` gives them
  their typed surface. Callable from Cure via `@extern(Elixir.Cure.Otp.Builtins, …)`.
  """

  @doc "Mint a fresh subject owned by the calling process: `{self(), make_ref()}`."
  def subject_new, do: {self(), make_ref()}

  @doc "Deliver a tagged message to the subject's owner. Returns `:ok`."
  def subject_send({owner, tag}, message) do
    send(owner, {tag, message})
    :ok
  end

  @doc """
  Tagged selective receive with a millisecond `timeout`. Only the owning process
  should call this. Returns the Cure `Option` representation — `{:some, message}`
  on receipt, `:none` on timeout.
  """
  def subject_receive({_owner, tag}, timeout) do
    receive do
      {^tag, message} -> {:some, message}
    after
      timeout -> :none
    end
  end

  # -- Selector: typed selective receive over several heterogeneous subjects -------------------------------
  #
  # A selector is `{:selector, handlers}` where `handlers` maps a subject's ref `tag` to its `transform`
  # (`payload -> payload'`). Subject messages are always the 2-tuple `{tag, payload}`, so `selector_receive` does
  # ONE receive matching `{tag, payload}` guarded by `is_map_key(tag, handlers)` — the dynamic multi-tag select
  # (the Subject-shaped case of Gleam's `gleam_erlang_ffi:select`). Unregistered messages stay in the mailbox.

  @doc "An empty selector."
  def selector_new, do: {:selector, %{}}

  @doc "Register `subject`'s messages, mapping each into the common payload via `transform`."
  def selector_select_map({:selector, handlers}, {_owner, tag}, transform) do
    {:selector, Map.put(handlers, tag, transform)}
  end

  @doc """
  Receive from whichever registered subject arrives first, within `timeout` ms, applying that subject's
  transform. Returns `{:some, payload}` or `:none` on timeout. Unregistered messages stay in the mailbox.
  """
  def selector_receive({:selector, handlers}, timeout) do
    receive do
      # NB: Elixir's `is_map_key/2` is `(map, key)` — the reverse of Erlang's `is_map_key(key, map)`.
      {tag, payload} when is_map_key(handlers, tag) ->
        {:some, Map.get(handlers, tag).(payload)}
    after
      timeout -> :none
    end
  end

  # -- Name: typed process registration (Std.Otp.Name / the F-1 typed name → handle) -----------------------
  #
  # A `Name(m)` is a registered atom carrying a phantom claim `m` about the message type its process accepts.
  # `name_whereis` returns the Cure `Option(Pid(m))` — a TYPED, sendable handle — rather than an untyped bare pid;
  # the type `m` rides on the `Name` (the trust point, exactly as Gleam's `Name(message)`). Register/unregister
  # are Bool-safe (Erlang `register/2` raises on a taken name or dead pid).

  @doc "Register `pid` under `name_atom`. Returns whether registration succeeded."
  def name_register(name_atom, pid) do
    :erlang.register(name_atom, pid)
    true
  rescue
    ArgumentError -> false
  end

  @doc "Look up the process registered under `name_atom` as a typed handle: `{:some, pid}` or `:none`."
  def name_whereis(name_atom) do
    case :erlang.whereis(name_atom) do
      :undefined -> :none
      pid -> {:some, pid}
    end
  end

  @doc "Remove the registration for `name_atom`. Returns whether it was registered."
  def name_unregister(name_atom) do
    :erlang.unregister(name_atom)
    true
  rescue
    ArgumentError -> false
  end
end
