# test/cure/migrate/edition_crossing_test.exs
defmodule Cure.Migrate.EditionCrossingTest do
  use ExUnit.Case, async: true
  alias Cure.Migrate

  test "rules_for_crossing includes every rule relevant to reaching the target, :manual included" do
    picked = Migrate.rules_for_crossing("2026", Migrate.rules()) |> Enum.map(& &1.id)
    # :machine, proactive (since <= target)
    assert :W_module_rename in picked
    # :review, proactive — must be included (§5.1/§7.2)
    assert :W_uppercase_type_var in picked

    # :manual is included too — NOT because it's tier-eligible for the
    # proactive clause (it isn't), but because its `enforced_in: "2026"` makes
    # it spec §7.2's "mandatory" bullet, which is tier-unrestricted. It has to
    # run through run_to_fixpoint so its {:warn, _} result actually fires and
    # lands in `warns` — that firing is the ONLY way Task 11's
    # plan_migration_source can detect it via blocking_manual and refuse the
    # edition bump. Excluding :manual rules here would make that detection
    # permanently vacuous (removed_module.ex's detect_and_rewrite always
    # returns {:warn, _}, never {:rewrite, _}, so its presence in this list
    # can never mutate the AST — only surface the warning).
    assert :W_removed_module in picked
  end

  test "blocking_manual reports :manual rules enforced at/before the target" do
    ids = Migrate.blocking_manual("2026", Migrate.rules()) |> Enum.map(& &1.id)
    assert :W_removed_module in ids
  end

  test "set_edition inserts an edition key under [project] losslessly" do
    dir = Path.join(System.tmp_dir!(), "cureset_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "Cure.toml")
    File.write!(path, "[project]\nname = \"demo\"\nversion = \"0.1.0\"\n")
    assert :ok = Cure.Project.set_edition(path, "2026")
    {:ok, project} = Cure.Project.load(dir)
    assert project.edition == "2026"
    # existing keys preserved
    assert project.name == "demo"
    assert project.version == "0.1.0"
  end

  test "set_edition replaces an existing edition key rather than duplicating it" do
    dir = Path.join(System.tmp_dir!(), "cureset2_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "Cure.toml")
    File.write!(path, "[project]\nname = \"demo\"\nedition = \"2026\"\n")
    assert :ok = Cure.Project.set_edition(path, "2026")
    body = File.read!(path)
    assert length(Regex.scan(~r/^edition = /m, body)) == 1
  end
end
