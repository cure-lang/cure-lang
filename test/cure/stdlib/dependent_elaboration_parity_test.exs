defmodule Cure.Stdlib.DependentElaborationParityTest do
  @moduledoc """
  #18-readiness firewall for the STANDARD LIBRARY. Every stdlib module listed in
  `@green` must elaborate on the DEPENDENT pipeline (`Cure.Elab.Program.elaborate/1`
  resolves `use` imports from `lib/std`). This locks the value-surface-parity work
  (#23) in as an immutable regression set: the classic pipeline
  (`lib/cure/compiler/codegen.ex`, `lib/cure/types/*`) is slated for deletion once
  the stdlib reaches full dependent parity, and until then a silent regression in
  ANY green module's dependent elaboration would otherwise go uncaught (only a
  handful of modules had individual `*_elaborates_test.exs` guards).

  The `@green` list only ever GROWS. The modules NOT listed are the known
  remaining blockers, documented for the rip-out ledger (do NOT assert they fail —
  that would freeze current brokenness; they are promoted into `@green` as they are
  fixed):

    * `access` — DELETED (2026-07-11). The only dependent-solvable route was an
      opaque `Any` top type + `believe_me` coercions dispatching on runtime
      `is_map`/`is_tuple` tags — a proliferation of unchecked casts that fought
      the type system rather than using it. Removed pending a well-typed redesign;
      not a rip-out blocker.
    * `io` — dependent-green WITH `use Std.String` + `use Std.Semigroup` (its `<>`
      routes through `Std.Semigroup.combine`), but the committed file omits those
      imports because the CLASSIC checker breaks on them (String=List(Char) vs
      binary). Pinned in the coexistence guard below; flips green the instant
      classic is deleted. (`show` was in this bucket until it was found that its
      committed file CAN carry the imports without breaking classic — now `@green`.)
    * `http`, `regex` — AtomVM dead-ends (`:inets`/`:re` absent); excluded from the
      parity target by design.
    * `pair` — bare-`Tuple`/`Any` shaped, slated for retirement in favour of
      `Std.Tuple` + `Std.Match`; excluded.

  Promoted into `@green`: `show` (imports added to the committed file, 5e303da) and
  `set` (the parameterised `Map(k, v)` that once made the classic checker reject
  `from_list`'s match with `E033` now joins cleanly — `type.ex` gained a covariant
  `Map`/same-constructor `{:adt}` subtype rule in bacf772 — so the fold-seeded
  functions could be rewritten as structural recursion in the committed file, the
  form `set_dependent_capability_test.exs` proves, and it elaborates on BOTH
  pipelines).
  """
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  # actor/app/fsm/process/supervisor were removed with the container compilers
  # (#18); concurrency is now pure `@extern` wrappers, not their own modules.
  @green ~w(
    atom binary bool bounded char comparable core crdt decision dynamic equatable
    equivalent float functor gen int iter json list map match math nat
    non_empty optic option proof result semigroup set show sigma string
    system telescope test time tuple unit vector
  )

  @tag timeout: 180_000
  test "every dependent-green stdlib module elaborates on the dependent pipeline" do
    failures =
      Enum.reduce(@green, [], fn name, acc ->
        path = Path.join("lib/std", name <> ".cure")

        result =
          try do
            Program.elaborate(File.read!(path))
          rescue
            e -> {:raise, Exception.message(e)}
          catch
            kind, value -> {:raise, "#{inspect(kind)}: #{inspect(value)}"}
          end

        case result do
          {:ok, _env} -> acc
          other -> [{name, inspect(other, limit: 5)} | acc]
        end
      end)

    assert failures == [],
           "stdlib modules regressed on the dependent pipeline:\n" <>
             Enum.map_join(Enum.reverse(failures), "\n", fn {n, e} -> "  Std.#{n}: #{e}" end)
  end

  # The classic-coexistence contract: `io` elaborates cleanly on the dependent
  # pipeline the instant it can carry its held-out imports (`use Std.String` +
  # `use Std.Semigroup`). The committed file omits those imports ONLY because the
  # CLASSIC checker breaks on them (String=List(Char) vs binary), so it cannot
  # appear in the `@green` scan above — but it flips green the moment classic is
  # deleted (#18). This guard locks that "green-on-deletion" property in as a
  # regression: a future break in `io`'s dependent side is caught HERE rather than
  # only at rip-out time. `io` genuinely needs BOTH imports (its `<>` routes
  # through `Std.Semigroup.combine`). `show` graduated OUT of this bucket into
  # `@green` — its committed file carries the imports without breaking classic.
  @coexistence [{"io", ~w(Std.String Std.Semigroup)}]

  test "classic-coexistence modules (io) elaborate once their held-out imports are added" do
    failures =
      Enum.reduce(@coexistence, [], fn {name, uses}, acc ->
        src = inject_uses(Path.join("lib/std", name <> ".cure"), uses)

        result =
          try do
            Program.elaborate(src)
          rescue
            e -> {:raise, Exception.message(e)}
          catch
            kind, value -> {:raise, "#{inspect(kind)}: #{inspect(value)}"}
          end

        case result do
          {:ok, _env} -> acc
          other -> [{name, inspect(other, limit: 5)} | acc]
        end
      end)

    assert failures == [],
           "classic-coexistence modules no longer elaborate with imports (green-on-" <>
             "deletion contract broken):\n" <>
             Enum.map_join(Enum.reverse(failures), "\n", fn {n, e} -> "  Std.#{n}: #{e}" end)
  end

  # Insert `use <mod>` lines immediately after the `mod …` header line, mirroring
  # how `Cure.Stdlib.Preload` would supply them once classic is gone.
  defp inject_uses(path, uses) do
    lines = String.split(File.read!(path), "\n")
    {pre, [mod_line | post]} = Enum.split_while(lines, &(not String.match?(&1, ~r/^\s*mod\s/)))
    use_lines = Enum.map(uses, &("  use " <> &1))
    Enum.join(pre ++ [mod_line] ++ use_lines ++ post, "\n")
  end
end
