defmodule Cure.CLI.MigrateEditionCLITest do
  use ExUnit.Case
  # These exercise the migrate command's pure planning path. Use the exposed
  # helper Cure.CLI is refactored to call (cmd_migrate delegates planning to a
  # testable function) rather than shelling out.

  test "a downgrade target is refused" do
    # "2025" is not a minted edition, but Cure.Edition.compare/2 is deliberately
    # allow-list-independent (Task 1) so a hypothetical older edition is a valid
    # probe here — plan_migration/1 only compares, it never validates target
    # against the known-editions allow-list (that happens earlier, when the
    # CLI's --edition flag is parsed via Cure.Edition.parse/1).
    assert {:error, :downgrade} = Cure.CLI.plan_migration(target: "2025", current: "2026")
  end

  test "a blocking :manual item prevents the edition bump" do
    # Build a source that references a removed module (Std.Refine) → :manual fires.
    src = "mod M\n  use Std.Refine\n  fn f(x: Int) -> Int = x\n"
    assert {:blocked, ids} = Cure.CLI.plan_migration_source(src, target: "2026")
    assert :W_removed_module in ids
  end

  test "a clean source migrates and reports a pending edition bump" do
    src = "mod M\n  use Std.Eq\n  fn f(x: Int) -> Bool = eq(x, x)\n"
    assert {:ok, out, _warns, bump} = Cure.CLI.plan_migration_source(src, target: "2026")
    assert out =~ "Std.Equatable"
    assert bump == "2026"
  end

  test "--strict promotes fixable-tier (:machine/:review) warnings but never :manual (spec §8)" do
    # a :machine warning (module rename) is promoted under strict
    fixable = "mod M\n  use Std.Eq\n  fn f(x: Int) -> Bool = eq(x, x)\n"

    assert {:error, {:strict_violation, ids}} =
             Cure.CLI.plan_migration_source(fixable, target: "2026", strict: true)

    assert :W_module_rename in ids

    # a :manual warning (removed module) is NOT promoted — it stays a block, not a strict error
    manual = "mod M\n  use Std.Refine\n  fn f(x: Int) -> Int = x\n"
    assert {:blocked, ids2} = Cure.CLI.plan_migration_source(manual, target: "2026", strict: true)
    assert :W_removed_module in ids2
  end
end
