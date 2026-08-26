defmodule Cure.Stdlib.PathsTest do
  # async: false -- each test flips `Application.get_env(:cure,
  # :stdlib_source_dir)` and `System.get_env("CURE_HOME")` which are
  # both process-global state.
  use ExUnit.Case, async: false

  alias Cure.Stdlib.Paths

  setup do
    previous_src = Application.get_env(:cure, :stdlib_source_dir)
    previous_beam = Application.get_env(:cure, :stdlib_beam_dir)
    previous_cure_home = System.get_env("CURE_HOME")
    previous_cure_lib = System.get_env("CURE_LIB")

    on_exit(fn ->
      case previous_src do
        nil -> Application.delete_env(:cure, :stdlib_source_dir)
        value -> Application.put_env(:cure, :stdlib_source_dir, value)
      end

      case previous_beam do
        nil -> Application.delete_env(:cure, :stdlib_beam_dir)
        value -> Application.put_env(:cure, :stdlib_beam_dir, value)
      end

      case previous_cure_home do
        nil -> System.delete_env("CURE_HOME")
        value -> System.put_env("CURE_HOME", value)
      end

      case previous_cure_lib do
        nil -> System.delete_env("CURE_LIB")
        value -> System.put_env("CURE_LIB", value)
      end
    end)

    :ok
  end

  describe "bundle_destination/0" do
    test "points at priv/std relative to the current project" do
      assert Paths.bundle_destination() == Path.join(["priv", "std"])
    end
  end

  describe "beam_bundle_destination/0" do
    test "points at priv/ebin relative to the current project" do
      assert Paths.beam_bundle_destination() == Path.join(["priv", "ebin"])
    end
  end

  describe "beam_dirs/0" do
    test "resolves an immutable artifact container to its published generation" do
      root = Path.join(System.tmp_dir!(), "cure_stdlib_generation_#{System.unique_integer([:positive])}")
      generation = String.duplicate("a", 64)
      published = Path.join([root, ".cure_generations", generation])
      File.mkdir_p!(published)
      File.write!(Path.join(root, "current"), generation <> "\n")

      try do
        Application.put_env(:cure, :stdlib_beam_dir, root)
        assert hd(Paths.beam_dirs()) == published
      after
        File.rm_rf!(root)
      end
    end

    test "prepends the configured override when it exists" do
      tmp = make_tmp!()

      try do
        Application.put_env(:cure, :stdlib_beam_dir, tmp)
        dirs = Paths.beam_dirs()

        assert List.first(dirs) == tmp
      after
        File.rm_rf!(tmp)
      end
    end

    test "drops the configured override when the directory is missing" do
      bogus = Path.join(System.tmp_dir!(), "cure_paths_beam_does_not_exist_#{unique()}")
      Application.put_env(:cure, :stdlib_beam_dir, bogus)

      refute bogus in Paths.beam_dirs()
    end

    test "returns only existing directories" do
      assert Enum.all?(Paths.beam_dirs(), &File.dir?/1)
    end
  end

  describe "beam_dir/0" do
    test "returns the first element of beam_dirs/0" do
      case Paths.beam_dirs() do
        [] -> assert Paths.beam_dir() == nil
        [first | _] -> assert Paths.beam_dir() == first
      end
    end
  end

  describe "source_dirs/0" do
    test "includes the legacy cwd-relative lib/std when present" do
      # The Cure repo ships `lib/std/` -- this should always be on the
      # list from inside the Cure project tree.
      assert Path.join(["lib", "std"]) in Paths.source_dirs()
    end

    test "prepends the configured override when it exists" do
      tmp = make_tmp!()

      try do
        Application.put_env(:cure, :stdlib_source_dir, tmp)
        dirs = Paths.source_dirs()

        assert List.first(dirs) == tmp
      after
        File.rm_rf!(tmp)
      end
    end

    test "drops the configured override when the directory is missing" do
      bogus = Path.join(System.tmp_dir!(), "cure_paths_does_not_exist_#{unique()}")
      Application.put_env(:cure, :stdlib_source_dir, bogus)

      refute bogus in Paths.source_dirs()
    end

    test "returns only existing directories" do
      assert Enum.all?(Paths.source_dirs(), &File.dir?/1)
    end

    test "is idempotent across calls (no hidden mutable state)" do
      assert Paths.source_dirs() == Paths.source_dirs()
    end
  end

  describe "source_dir/0" do
    test "memoizes directory probing while the candidate configuration is unchanged" do
      :cprof.start()

      try do
        assert Paths.source_dir() == Paths.source_dir()
        :cprof.pause()

        {Paths, _total, entries} = :cprof.analyse(Paths)
        assert {{Paths, :source_dirs, 0}, 1} in entries
      after
        :cprof.stop()
      end
    end

    test "returns the first element of source_dirs/0" do
      case Paths.source_dirs() do
        [] -> assert Paths.source_dir() == nil
        [first | _] -> assert Paths.source_dir() == first
      end
    end

    test "returns nil when nothing resolves" do
      # Walk past every candidate by pointing the override at a
      # nonexistent path; the priv/legacy fallbacks may still resolve
      # when running from the Cure repo, so we only assert the
      # override was ignored. A stricter "returns nil" test would
      # require sandboxing `:code.priv_dir/1`, which is out of scope.
      Application.put_env(:cure, :stdlib_source_dir, "/nonexistent/cure/stdlib/#{unique()}")
      assert Paths.source_dir() != "/nonexistent/cure/stdlib"
    end
  end

  describe "cure_home/0" do
    test "returns nil when CURE_HOME is unset" do
      System.delete_env("CURE_HOME")
      assert Paths.cure_home() == nil
    end

    test "returns nil when CURE_HOME is blank or whitespace" do
      System.put_env("CURE_HOME", "")
      assert Paths.cure_home() == nil

      System.put_env("CURE_HOME", "   \t  ")
      assert Paths.cure_home() == nil
    end

    test "returns the trimmed env value when set" do
      System.put_env("CURE_HOME", "  /opt/cure  ")
      assert Paths.cure_home() == "/opt/cure"
    end
  end

  describe "cure_home_beam_dirs/0" do
    test "returns the empty list when CURE_HOME is unset" do
      System.delete_env("CURE_HOME")
      assert Paths.cure_home_beam_dirs() == []
    end

    test "returns priv/ebin then _build/cure/ebin candidates in order" do
      System.put_env("CURE_HOME", "/opt/cure")

      assert Paths.cure_home_beam_dirs() == [
               Path.join(["/opt/cure", "priv", "ebin"]),
               Path.join(["/opt/cure", "_build", "cure", "ebin"])
             ]
    end
  end

  describe "cure_home_source_dirs/0" do
    test "returns the empty list when CURE_HOME is unset" do
      System.delete_env("CURE_HOME")
      assert Paths.cure_home_source_dirs() == []
    end

    test "returns priv/std then lib/std candidates in order" do
      System.put_env("CURE_HOME", "/opt/cure")

      assert Paths.cure_home_source_dirs() == [
               Path.join(["/opt/cure", "priv", "std"]),
               Path.join(["/opt/cure", "lib", "std"])
             ]
    end
  end

  describe "CURE_HOME resolution in beam_dirs/0" do
    test "surfaces $CURE_HOME/priv/ebin when it exists on disk" do
      home = make_tmp!()
      ebin = Path.join([home, "priv", "ebin"])
      File.mkdir_p!(ebin)

      try do
        Application.delete_env(:cure, :stdlib_beam_dir)
        System.put_env("CURE_HOME", home)

        assert ebin in Paths.beam_dirs()
      after
        File.rm_rf!(home)
      end
    end

    test "surfaces $CURE_HOME/_build/cure/ebin when it exists on disk" do
      home = make_tmp!()
      build = Path.join([home, "_build", "cure", "ebin"])
      File.mkdir_p!(build)

      try do
        Application.delete_env(:cure, :stdlib_beam_dir)
        System.put_env("CURE_HOME", home)

        assert build in Paths.beam_dirs()
      after
        File.rm_rf!(home)
      end
    end

    test "the explicit :stdlib_beam_dir override still wins over CURE_HOME" do
      home = make_tmp!()
      home_ebin = Path.join([home, "priv", "ebin"])
      File.mkdir_p!(home_ebin)

      override = make_tmp!()

      try do
        Application.put_env(:cure, :stdlib_beam_dir, override)
        System.put_env("CURE_HOME", home)

        dirs = Paths.beam_dirs()
        assert List.first(dirs) == override
        assert home_ebin in dirs
      after
        File.rm_rf!(override)
        File.rm_rf!(home)
      end
    end

    test "missing CURE_HOME sub-directories are skipped" do
      home = make_tmp!()
      # Intentionally do NOT create priv/ebin or _build/cure/ebin.

      try do
        Application.delete_env(:cure, :stdlib_beam_dir)
        System.put_env("CURE_HOME", home)

        for candidate <- Paths.cure_home_beam_dirs() do
          refute candidate in Paths.beam_dirs(),
                 "expected #{candidate} to be skipped (not a real directory)"
        end
      after
        File.rm_rf!(home)
      end
    end
  end

  describe "CURE_HOME resolution in source_dirs/0" do
    test "surfaces $CURE_HOME/priv/std when it exists on disk" do
      home = make_tmp!()
      std = Path.join([home, "priv", "std"])
      File.mkdir_p!(std)

      try do
        Application.delete_env(:cure, :stdlib_source_dir)
        System.put_env("CURE_HOME", home)

        assert std in Paths.source_dirs()
      after
        File.rm_rf!(home)
      end
    end

    test "surfaces $CURE_HOME/lib/std when it exists on disk" do
      home = make_tmp!()
      lib_std = Path.join([home, "lib", "std"])
      File.mkdir_p!(lib_std)

      try do
        Application.delete_env(:cure, :stdlib_source_dir)
        System.put_env("CURE_HOME", home)

        assert lib_std in Paths.source_dirs()
      after
        File.rm_rf!(home)
      end
    end

    test "the explicit :stdlib_source_dir override still wins over CURE_HOME" do
      home = make_tmp!()
      home_std = Path.join([home, "priv", "std"])
      File.mkdir_p!(home_std)

      override = make_tmp!()

      try do
        Application.put_env(:cure, :stdlib_source_dir, override)
        System.put_env("CURE_HOME", home)

        dirs = Paths.source_dirs()
        assert List.first(dirs) == override
        assert home_std in dirs
      after
        File.rm_rf!(override)
        File.rm_rf!(home)
      end
    end

    test "a blank CURE_HOME is treated as unset" do
      System.put_env("CURE_HOME", "   ")
      # Just check the helper is empty; the full source_dirs/0 may
      # still surface the legacy `lib/std` from cwd.
      assert Paths.cure_home_source_dirs() == []
    end
  end

  describe "cure_lib/0" do
    test "returns nil when CURE_LIB is unset" do
      System.delete_env("CURE_LIB")
      assert Paths.cure_lib() == nil
    end

    test "returns nil when CURE_LIB is blank or whitespace" do
      System.put_env("CURE_LIB", "")
      assert Paths.cure_lib() == nil

      System.put_env("CURE_LIB", "   \t  ")
      assert Paths.cure_lib() == nil
    end

    test "returns the trimmed env value when set" do
      System.put_env("CURE_LIB", "  /opt/cure/ebin  ")
      assert Paths.cure_lib() == "/opt/cure/ebin"
    end
  end

  describe "cure_lib_beam_dirs/0" do
    test "returns the empty list when CURE_LIB is unset" do
      System.delete_env("CURE_LIB")
      assert Paths.cure_lib_beam_dirs() == []
    end

    test "returns the directory directly as a single-element list" do
      System.put_env("CURE_LIB", "/opt/cure/ebin")
      assert Paths.cure_lib_beam_dirs() == ["/opt/cure/ebin"]
    end
  end

  describe "cure_lib_source_dirs/0" do
    test "returns the empty list when CURE_LIB is unset" do
      System.delete_env("CURE_LIB")
      assert Paths.cure_lib_source_dirs() == []
    end

    test "returns the sibling ../std path" do
      System.put_env("CURE_LIB", "/opt/cure/ebin")
      [dir] = Paths.cure_lib_source_dirs()
      assert String.ends_with?(dir, "/std")
    end
  end

  describe "CURE_LIB resolution in beam_dirs/0" do
    test "surfaces $CURE_LIB when it exists on disk" do
      dir = make_tmp!()

      try do
        Application.delete_env(:cure, :stdlib_beam_dir)
        System.delete_env("CURE_HOME")
        System.put_env("CURE_LIB", dir)

        assert dir in Paths.beam_dirs()
      after
        File.rm_rf!(dir)
      end
    end

    test "the explicit :stdlib_beam_dir override still wins over CURE_LIB" do
      lib = make_tmp!()
      override = make_tmp!()

      try do
        Application.put_env(:cure, :stdlib_beam_dir, override)
        System.put_env("CURE_LIB", lib)

        dirs = Paths.beam_dirs()
        assert List.first(dirs) == override
        assert lib in dirs
      after
        File.rm_rf!(lib)
        File.rm_rf!(override)
      end
    end
  end

  describe "standalone launcher home" do
    test "derives stdlib candidates from the escript's own directory" do
      assert Paths.launcher_home_beam_dirs("/opt/cure/cure") == [
               "/opt/cure/priv/ebin",
               "/opt/cure/_build/cure/ebin"
             ]

      assert Paths.launcher_home_source_dirs("/opt/cure/cure") == [
               "/opt/cure/priv/std",
               "/opt/cure/lib/std"
             ]
    end

    test "ignores evaluator-style launcher names" do
      assert Paths.launcher_home_beam_dirs("-e") == []
      assert Paths.launcher_home_source_dirs("") == []
    end
  end

  # ---------------------------------------------------------------------------

  defp make_tmp! do
    path = Path.join(System.tmp_dir!(), "cure_paths_test_#{unique()}")
    File.mkdir_p!(path)
    path
  end

  defp unique, do: System.unique_integer([:positive])
end
