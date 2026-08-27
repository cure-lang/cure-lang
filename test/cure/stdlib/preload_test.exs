defmodule Cure.Stdlib.PreloadTest do
  # async: false -- the preload stanza mutates `:cure` application
  # env entries (`:stdlib_beam_dir`, `:stdlib_source_dir`) which are
  # process-global state.
  use ExUnit.Case, async: false

  alias Cure.Stdlib.Preload

  describe "known_groups/0" do
    test "returns the canonical list of stdlib groups" do
      groups = Preload.known_groups()

      assert :core in groups
      assert :collections in groups
      assert :text in groups
      assert :numeric in groups
      assert :system in groups
      assert :concurrency in groups
      assert :option in groups
      assert :test in groups
      assert :network in groups
    end
  end

  describe "module_groups/0" do
    test "is built at compile time from lib/std/*.cure" do
      groups = Preload.module_groups()

      assert is_map(groups)
      assert Map.get(groups, :"Cure.Std.Core") == :core
      assert Map.get(groups, :"Cure.Std.List") == :collections
      assert Map.get(groups, :"Cure.Std.Math") == :numeric
      assert Map.get(groups, :"Cure.Std.Option") == :option
    end
  end

  describe "stdlib_modules/1" do
    test ":none returns the empty list (default)" do
      assert Preload.stdlib_modules() == []
      assert Preload.stdlib_modules(:none) == []
    end

    test ":all returns every known stdlib module" do
      mods = Preload.stdlib_modules(:all)

      # Sanity check a handful of modules we know must be present.
      for m <- [:"Cure.Std.Core", :"Cure.Std.List", :"Cure.Std.Math", :"Cure.Std.Option"] do
        assert m in mods
      end

      assert length(mods) == map_size(Preload.module_groups())
    end

    test ":core matches the modules explicitly described in the spec" do
      core = Preload.stdlib_modules(:core)

      # The user-facing spec requires these exact modules under :core.
      required = ~w(Core Equivalent Equatable Comparable Show Functor)a

      for short <- required do
        module = String.to_atom("Cure.Std.#{short}")
        assert module in core, "expected #{inspect(module)} in :core"
      end

      refute :"Cure.Std.List" in core
    end

    test "a single-group atom filters to that group" do
      collections = Preload.stdlib_modules(:collections)
      assert :"Cure.Std.List" in collections
      assert :"Cure.Std.Map" in collections
      refute :"Cure.Std.Core" in collections
    end

    test "a list of groups unions their membership with no duplicates" do
      merged = Preload.stdlib_modules([:core, :option, :option])
      assert :"Cure.Std.Core" in merged
      assert :"Cure.Std.Option" in merged
      assert :"Cure.Std.Result" in merged
      assert merged == Enum.uniq(merged)
    end

    test "unknown kind atom raises ArgumentError" do
      assert_raise ArgumentError, fn -> Preload.stdlib_modules(:bogus) end
    end

    test "non-atom / non-list kind raises ArgumentError" do
      assert_raise ArgumentError, fn -> Preload.stdlib_modules("core") end
      assert_raise ArgumentError, fn -> Preload.stdlib_modules(42) end
    end

    test "unknown group inside a list raises ArgumentError" do
      assert_raise ArgumentError, fn -> Preload.stdlib_modules([:core, :bogus]) end
    end
  end

  describe "preload/1" do
    test ":none (default) returns :ok without touching the VM" do
      assert Preload.preload() == :ok
      assert Preload.preload(kind: :none) == :ok
    end

    test "kind: :all loads every known stdlib module" do
      assert Preload.preload(examples: false, kind: :all) == :ok

      # A representative sample should be loaded after the call.
      assert Code.ensure_loaded?(:"Cure.Std.Core")
      assert Code.ensure_loaded?(:"Cure.Std.List")
    end

    # Under C1 the canonical stdlib is already loaded (and sticky) by the time
    # any test runs (test/test_helper.exs). The moduledoc promises "modules
    # already loaded into the VM are left alone", but the loader used to
    # unconditionally retry `:code.load_binary/3` on every module in the
    # closure regardless of residency -- against a sticky module that retry
    # is rejected by OTP, and the rejection is logged at `:error` level as a
    # side effect independent of the (correctly tolerated) Elixir-level
    # return value. With ~70 stdlib modules and roughly a dozen call sites
    # across the suite (every migrated C2/C3 test's `setup_all` calls
    # `preload(kind: :all)` after C1 has already stuck everything), this
    # floods CI output with hundreds of spurious `[error]` lines that can
    # bury genuine failures.
    test "kind: :all is silent when every module is already loaded" do
      # Precondition: test_helper.exs already loaded+stuck the canonical
      # stdlib before any test ran.
      assert Code.ensure_loaded?(:"Cure.Std.Core")

      log =
        ExUnit.CaptureLog.capture_log(fn ->
          assert Preload.preload(examples: false, kind: :all) == :ok
        end)

      refute log =~ "sticky dir"
    end

    test "unknown kind raises ArgumentError" do
      assert_raise ArgumentError, fn -> Preload.preload(kind: :bogus) end
    end

    # Regression for the production Yeesh REPL: in a release,
    # `_build/cure/ebin` is absent and the bundled `priv/ebin/` is the
    # only place stdlib BEAMs live. The stanza below pretends `priv/ebin/`
    # is elsewhere on disk and asserts the preload picks it up.
    test "honours :stdlib_beam_dir app-env override" do
      tmp = make_tmp!()
      module = :"Cure.Std.Core"

      assert {:ok, resident_set} =
               Cure.Compiler.Artifacts.open_verified_set(
                 kind: :stdlib,
                 candidates: Cure.Stdlib.Paths.beam_dirs(),
                 verification: :full
               )

      assert {:ok, _} = Cure.Compiler.Artifacts.copy_verified_set(resident_set.artifact_root, tmp)

      previous = Application.get_env(:cure, :stdlib_beam_dir)
      Application.put_env(:cure, :stdlib_beam_dir, tmp)

      try do
        assert Preload.preload(kind: :all, source_jit: false) == :ok
        assert Code.ensure_loaded?(module)
      after
        case previous do
          nil -> Application.delete_env(:cure, :stdlib_beam_dir)
          value -> Application.put_env(:cure, :stdlib_beam_dir, value)
        end

        File.rm_rf!(tmp)
      end

      assert :code.is_sticky(module)
    end

    test "rejects an unmanifested partial override instead of mixing candidates" do
      tmp = make_tmp!()
      canonical = Cure.Stdlib.Paths.beam_dir() || Cure.Compiler.Artifacts.Writer.resolve("_build/cure/ebin")
      File.cp!(Path.join(canonical, "Cure.Std.Core.beam"), Path.join(tmp, "Cure.Std.Core.beam"))

      assert {:error, {:no_verified_artifact_set, _}} =
               Preload.preload(
                 kind: :all,
                 stdlib_ebin: tmp,
                 source_jit: false
               )
    end
  end

  # ---------------------------------------------------------------------------

  defp make_tmp! do
    path =
      Path.join(System.tmp_dir!(), "cure_preload_test_#{System.unique_integer([:positive])}")

    File.mkdir_p!(path)
    path
  end
end
