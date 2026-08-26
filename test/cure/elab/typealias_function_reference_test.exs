defmodule Cure.Elab.TypealiasFunctionReferenceTest do
  @moduledoc """
  A `typealias` body may name a module-level function.

  This is not an exotic capability: `Std.Otp.DepActorServer(m, q, rep)` takes its
  reply family as a *value* — `rep : (q) -> Type` — so the `actor` macro emits

      fn ReplyOf(request: ActorRequest) -> Type = ...
      typealias Handle = Std.Otp.DepActorServer(Message, Request, ReplyOf)

  into every query-bearing actor. Without this, `actor ... on_call` cannot be
  compiled at all (E092, "`ReplyOf` is not available in this value namespace").

  The cause was declaration ordering, not scoping. `register_pass/3` ran
  `declare_type_headers` → `complete_typealiases` → `body_register_pass`, so
  every alias body was elaborated *before* a single function signature existed.
  A module is one mutually-recursive block, so an alias naming a function was
  rejected outright even though the function was declared above it.

  A module-scope alias and a module-scope function may now refer to each other in
  either direction. A genuinely unknown name is still an error — it is reported by
  the second, authoritative `complete_typealiases` pass, which runs against the
  fully-populated environment.
  """
  # The end-to-end regression loads a generated actor module into the VM-global
  # code server. Keep this module out of the async pool so a timed-out compiler
  # cannot continue code loading underneath later BEAM golden tests.
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  test "a typealias may apply a module-level function" do
    src = """
    mod M
      type Request = Value() | Bump(Int)

      fn ReplyOf(request: Request) -> Type = match request
        Value() -> Int
        Bump(_) -> Int

      typealias Answer = ReplyOf(Value())

      fn answer(x: Answer) -> Answer = x
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a typealias may pass a module-level function unapplied as a type argument" do
    # The shape the `actor` macro emits: the reply family crosses into
    # `DepActorServer` as a value of type `(q) -> Type`, not as an application.
    src = """
    mod M
      type Request = Value() | Bump(Int)

      fn ReplyOf(request: Request) -> Type = match request
        Value() -> Int
        Bump(_) -> Int

      typealias Handle = Std.Otp.DepActorServer(Unit, Request, ReplyOf)
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a function declared below the alias is in scope too: a module is one block" do
    src = """
    mod M
      type Request = Value() | Bump(Int)

      typealias Answer = ReplyOf(Value())

      fn ReplyOf(request: Request) -> Type = match request
        Value() -> Int
        Bump(_) -> Int
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "a genuinely unknown name in an alias body is still rejected" do
    src = """
    mod M
      typealias Answer = NoSuchFunction(3)
    end
    """

    assert {:error, _} = Program.elaborate(src)
  end

  test "an actor with a typed query compiles end to end" do
    # The regression this exists for: every `on_call`-bearing actor failed with
    # E092 because its generated `Handle` alias named the generated `ReplyOf`.
    src = """
    use Std.Actor

    actor Counter
      state Int
      initial 0
      on_call Value() returns Int
        reply state
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(src, emit_events: false)
  end

  test "a typed actor compile does not poison a later preloaded compilation" do
    actor = """
    use Std.Actor

    actor CacheIsolationCounter
      state Int
      initial 0
      on_call Value() returns Int
        reply state
    """

    assert {:ok, _module} = Cure.Compiler.compile_and_load(actor, emit_events: false)

    root = File.cwd!()
    stdlib_source = Path.expand("lib/std", root)

    assert {:ok, resident_set} =
             Cure.Compiler.Artifacts.open_verified_set(
               kind: :stdlib,
               candidates: Cure.Stdlib.Paths.beam_dirs(),
               verification: :full
             )

    stdlib_ebin = resident_set.artifact_root
    previous_cure_lib = System.get_env("CURE_LIB")
    previous_source = Application.get_env(:cure, :stdlib_source_dir)
    previous_ebin = Application.get_env(:cure, :stdlib_beam_dir)

    on_exit(fn ->
      if previous_cure_lib,
        do: System.put_env("CURE_LIB", previous_cure_lib),
        else: System.delete_env("CURE_LIB")

      restore_application_env(:stdlib_source_dir, previous_source)
      restore_application_env(:stdlib_beam_dir, previous_ebin)
    end)

    System.put_env("CURE_LIB", stdlib_ebin)
    Application.put_env(:cure, :stdlib_source_dir, stdlib_source)
    Application.put_env(:cure, :stdlib_beam_dir, stdlib_ebin)
    assert :ok = Cure.Stdlib.Preload.preload(kind: :all, stdlib_ebin: stdlib_ebin, source_jit: false)

    source = "mod AfterActor\n  fn answer() -> Int = 42\n"

    assert {:ok, _module} =
             Cure.Compiler.compile_and_load(source,
               file: "after_actor.cure",
               source_roots: [Path.expand("lib", root), stdlib_source],
               emit_events: false
             )
  end

  defp restore_application_env(key, nil), do: Application.delete_env(:cure, key)
  defp restore_application_env(key, value), do: Application.put_env(:cure, key, value)
end
