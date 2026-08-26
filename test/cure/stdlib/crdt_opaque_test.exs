defmodule Cure.Stdlib.CrdtOpaqueTest do
  @moduledoc """
  `Std.CRDT`'s counter/set/register types are opaque handles to runtime state
  managed entirely through `@extern` calls to `:cure_std_crdt` — no Cure code
  constructs or projects them. They were declared as records with an *undeclared*
  field type variable (`rec GCounter\n counts: t`), which the dependent
  elaborator rejects: the free `t` reaches the kernel as an unbound `{:global, :t}`
  (`:unknown_global`). Modelled correctly as `opaque type` carriers (Agda
  `postulate` — inhabited, non-eliminable), the module elaborates and the handles
  thread through the typed `@extern` API.
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  test "Std.Crdt elaborates on the dependent pipeline" do
    assert {:ok, _env} = Program.elaborate(File.read!("lib/std/crdt.cure"))
  end

  test "an opaque GCounter handle threads through the extern API in a client module" do
    src = """
    mod M
      use Std.CRDT
      fn bump(node: Atom) -> Int =
        let c = g_increment(g_empty(), node, 5)
        g_value(c)
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  test "replica identities are application types rather than forced atoms" do
    src = """
    mod TypedReplica
      use Std.CRDT

      type Replica = Sydney | Melbourne

      fn count() -> Int =
        let a = g_increment(g_empty(), Sydney(), 2)
        let b = g_increment(g_empty(), Melbourne(), 3)
        g_value(g_merge(a, b))
    """

    assert {:ok, _env} = Program.elaborate(src)
  end
end
