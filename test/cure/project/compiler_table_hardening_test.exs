defmodule Cure.Project.CompilerTableHardeningTest do
  use ExUnit.Case, async: false

  # The `[compiler]` table converted every key to an atom via String.to_atom/1
  # (project.ex:1088). A Cure.toml is arbitrary user bytes, so this had two
  # defects, both of the same class as the value-column non-UTF-8 fix:
  #   1. a non-UTF-8 key byte made String.to_atom/1 raise ArgumentError, crashing
  #      every project-loading command (build/run/migrate);
  #   2. each distinct unknown key permanently interned a fresh atom — an
  #      atom-table exhaustion DoS from a large or malicious manifest (or a
  #      dependency's).
  # Only `type_check`, `optimize`, and `stdlib_path` are ever read; every other
  # `[compiler]` key is stored-but-never-consumed, so the fix recognizes the
  # known keys and drops the rest (never interning arbitrary input).

  defp write(dir, toml), do: File.write!(Path.join(dir, "Cure.toml"), toml)

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "cure_ctbl_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    ExUnit.Callbacks.on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  test "a non-UTF-8 byte in a [compiler] key does not crash load" do
    dir = tmp()
    write(dir, "[project]\nname = \"x\"\nedition = \"2026\"\n[compiler]\ncaf" <> <<0xE9>> <> "_mode = true\n")

    assert {:ok, %{edition: "2026"}} = Cure.Project.load(dir)
  end

  test "an unrecognized [compiler] key is ignored, not interned as a fresh atom" do
    dir = tmp()
    key = "zz_unknown_flag_#{System.unique_integer([:positive])}"
    write(dir, "[project]\nname = \"x\"\nedition = \"2026\"\n[compiler]\n#{key} = true\n")

    assert {:ok, _} = Cure.Project.load(dir)

    # If the key had been interned, String.to_existing_atom would succeed. It
    # must raise — proving the DoS surface (one atom per distinct key) is closed.
    assert_raise ArgumentError, fn -> String.to_existing_atom(key) end
  end

  test "recognized boolean keys still flow through to compiler_opts" do
    dir = tmp()
    write(dir, "[project]\nname = \"x\"\nedition = \"2026\"\n[compiler]\ntype_check = true\noptimize = true\n")

    {:ok, project} = Cure.Project.load(dir)
    opts = Cure.Project.compiler_opts(project)
    assert Keyword.get(opts, :check_types) == true
    assert Keyword.get(opts, :optimize) == true
  end
end
