defmodule Cure.Project.LoadNonUtf8Test do
  use ExUnit.Case, async: true

  # A Cure.toml is arbitrary user-authored bytes. A value line carrying a
  # non-UTF-8 byte (e.g. a latin-1 `café` with 0xE9) reached
  # strip_inline_comment/1, whose String.to_charlist/1 raised a
  # UnicodeConversionError — an uncaught crash on every project-loading command
  # (build/run/migrate). load/1 must instead complete (returning {:ok, _} for an
  # otherwise-valid manifest), never raise.
  test "load/1 does not crash on a value line with a non-UTF-8 byte" do
    dir = Path.join(System.tmp_dir!(), "cure_nonutf8_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)

    # `name = "caf<0xE9>"` — a bare latin-1 é, invalid UTF-8. Written as raw bytes.
    toml = "[project]\nname = \"caf" <> <<0xE9>> <> "\"\nedition = \"2026\"\n"
    File.write!(Path.join(dir, "Cure.toml"), toml)

    assert {:ok, %{edition: "2026"}} = Cure.Project.load(dir)
  end

  test "a non-UTF-8 byte after a value's inline-comment marker is still dropped cleanly" do
    dir = Path.join(System.tmp_dir!(), "cure_nonutf8b_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)

    toml = "[project]\nname = \"ok\"  # note caf" <> <<0xE9>> <> "\nedition = \"2026\"\n"
    File.write!(Path.join(dir, "Cure.toml"), toml)

    assert {:ok, %{name: "ok", edition: "2026"}} = Cure.Project.load(dir)
  end
end
