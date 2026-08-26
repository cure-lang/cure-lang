defmodule Cure.REPL.ConfigTest do
  # async: false -- `load/0` inspects `File.cwd!/0` and `System.user_home!/0`,
  # both of which are process-global from ExUnit's point of view.
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Cure.REPL.Config

  describe "defaults/0" do
    test "returns preload: :all, imports: :none" do
      assert Config.defaults() == %{preload: :all, imports: :none}
    end
  end

  describe "parse_stdlib/1" do
    test "nil maps to :none" do
      assert Config.parse_stdlib(nil) == :none
    end

    test "'none' / 'all' string values normalise to their atoms" do
      assert Config.parse_stdlib("none") == :none
      assert Config.parse_stdlib("  NONE ") == :none
      assert Config.parse_stdlib("all") == :all
      assert Config.parse_stdlib("ALL") == :all
    end

    test "a known group string maps to the matching atom" do
      assert Config.parse_stdlib("core") == :core
      assert Config.parse_stdlib("collections") == :collections
    end

    test "an unknown group string falls back to :none with a warning" do
      out = capture_io(:stderr, fn -> assert Config.parse_stdlib("bogus") == :none end)
      assert out =~ "unknown stdlib group"
    end

    test "an empty list maps to :none" do
      assert Config.parse_stdlib([]) == :none
    end

    test "a single-element list returns the atom directly" do
      assert Config.parse_stdlib(["core"]) == :core
    end

    test "multiple groups are returned as a deduped atom list" do
      assert Config.parse_stdlib(["core", "collections", "core"]) ==
               [:core, :collections]
    end

    test "'all' inside a list short-circuits to every known group" do
      result = Config.parse_stdlib(["core", "all"])
      assert is_list(result)
      assert :core in result
      assert :collections in result
      assert :network in result
    end

    test "unknown entries in a list are dropped with a warning" do
      out =
        capture_io(:stderr, fn ->
          assert Config.parse_stdlib(["core", "bogus"]) == :core
        end)

      assert out =~ "unknown stdlib group"
    end

    test "non-string entries are ignored with a warning" do
      out =
        capture_io(:stderr, fn ->
          assert Config.parse_stdlib(["core", 42]) == :core
        end)

      assert out =~ "non-string stdlib group"
    end

    test "values of an unexpected shape fall back to :none with a warning" do
      out = capture_io(:stderr, fn -> assert Config.parse_stdlib(42) == :none end)
      assert out =~ "unrecognised"
    end
  end

  describe "from_parsed/1" do
    test "empty document yields the defaults" do
      assert Config.from_parsed(%{}) == %{preload: :all, imports: :none}
    end

    test "missing [stdlib] section yields the defaults" do
      assert Config.from_parsed(%{"other" => %{"key" => "value"}}) == %{preload: :all, imports: :none}
    end

    test "picks up the [stdlib] preload value" do
      assert Config.from_parsed(%{"stdlib" => %{"preload" => "all"}}) ==
               %{preload: :all, imports: :none}

      assert Config.from_parsed(%{"stdlib" => %{"preload" => "none"}}) ==
               %{preload: :none, imports: :none}

      assert Config.from_parsed(%{"stdlib" => %{"preload" => ["core"]}}) ==
               %{preload: :core, imports: :none}

      assert Config.from_parsed(%{"stdlib" => %{"preload" => ["core", "collections"]}}) ==
               %{preload: [:core, :collections], imports: :none}
    end

    test "picks up the [stdlib] imports value" do
      assert Config.from_parsed(%{"stdlib" => %{"imports" => "all"}}) ==
               %{preload: :all, imports: :all}

      assert Config.from_parsed(%{"stdlib" => %{"imports" => ["core"]}}) ==
               %{preload: :all, imports: :core}
    end

    test "preload and imports are independent" do
      assert Config.from_parsed(%{"stdlib" => %{"preload" => "none", "imports" => "core"}}) ==
               %{preload: :none, imports: :core}
    end
  end

  describe "load/0" do
    setup context do
      # Move into a private tmp directory and swap $HOME so load/0 sees a
      # clean slate regardless of any real config the developer has.
      original_home = System.get_env("HOME")
      original_cwd = File.cwd!()

      tmp =
        Path.join(
          System.tmp_dir!(),
          "cure-repl-config-#{context.test}-#{System.unique_integer([:positive])}"
        )

      File.mkdir_p!(tmp)

      fake_home = Path.join(tmp, "home")
      fake_cwd = Path.join(tmp, "cwd")
      File.mkdir_p!(fake_home)
      File.mkdir_p!(fake_cwd)

      System.put_env("HOME", fake_home)
      File.cd!(fake_cwd)

      on_exit(fn ->
        File.cd!(original_cwd)

        if original_home do
          System.put_env("HOME", original_home)
        else
          System.delete_env("HOME")
        end

        File.rm_rf!(tmp)
      end)

      %{home: fake_home, cwd: fake_cwd}
    end

    test "returns defaults when neither file exists" do
      assert Config.load() == %{preload: :all, imports: :none}
    end

    test "reads ~/.cure.repl.toml when no cwd override is present", %{home: home} do
      File.write!(
        Path.join(home, ".cure.repl.toml"),
        """
        [stdlib]
        preload = "all"
        """
      )

      assert Config.load() == %{preload: :all, imports: :none}
    end

    test "cwd file overrides the home-wide one", %{home: home, cwd: cwd} do
      File.write!(
        Path.join(home, ".cure.repl.toml"),
        """
        [stdlib]
        preload = "all"
        """
      )

      File.write!(
        Path.join(cwd, ".cure.repl.toml"),
        """
        [stdlib]
        preload = ["core"]
        """
      )

      assert Config.load() == %{preload: :core, imports: :none}
    end

    test "imports key is loaded from file", %{cwd: cwd} do
      File.write!(
        Path.join(cwd, ".cure.repl.toml"),
        """
        [stdlib]
        imports = "core"
        """
      )

      assert Config.load() == %{preload: :all, imports: :core}
    end

    test "malformed TOML falls back to defaults with a warning", %{cwd: cwd} do
      File.write!(Path.join(cwd, ".cure.repl.toml"), "this is =[not\n valid toml")

      out = capture_io(:stderr, fn -> assert Config.load() == %{preload: :all, imports: :none} end)
      assert out =~ "failed to parse"
      assert out =~ "[W002]"
      assert length(Regex.scan(~r/-- INVALID CONFIGURATION \[W002\]/, out)) == 1
      refute out =~ "INVALID CONFIGURATION [W002].*INVALID CONFIGURATION"
      refute out =~ "{:"
    end
  end
end
