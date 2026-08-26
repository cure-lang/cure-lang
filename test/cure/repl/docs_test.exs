defmodule Cure.REPL.DocsTest do
  # async: false -- one test flips `Application.put_env(:cure,
  # :stdlib_source_dir, ...)` which is process-global state.
  use ExUnit.Case, async: false

  alias Cure.REPL.Docs
  alias Cure.REPL.Theme

  describe "parse_target/1" do
    test "module with dotted path" do
      assert {:ok, {:module, "Std.List"}} = Docs.parse_target("Std.List")
    end

    test "strips leading Cure. prefix" do
      assert {:ok, {:module, "Std.List"}} = Docs.parse_target("Cure.Std.List")
    end

    test "single PascalCase name is a module" do
      assert {:ok, {:module, "List"}} = Docs.parse_target("List")
    end

    test "last segment lowercase => function" do
      assert {:ok, {:function, "Std.List", "map"}} = Docs.parse_target("Std.List.map")
      assert {:ok, {:function, "Std.List", "map"}} = Docs.parse_target("Cure.Std.List.map")
    end

    test "bare lowercase name is rejected" do
      assert {:error, _} = Docs.parse_target("map")
    end

    test "empty input is rejected" do
      assert {:error, _} = Docs.parse_target("")
    end
  end

  describe "default_uses/1" do
    test "defaults to :none and returns the empty list" do
      assert Docs.default_uses() == []
      assert Docs.default_uses(:none) == []
    end

    test ":all returns Cure-prefix-free stdlib names" do
      defaults = Docs.default_uses(:all)

      assert is_list(defaults)
      assert "Std.Core" in defaults
      assert "Std.List" in defaults

      refute Enum.any?(defaults, &String.starts_with?(&1, "Cure."))
    end

    test ":all matches the Preload module list" do
      defaults = Docs.default_uses(:all)
      preload_count = length(Cure.Stdlib.Preload.stdlib_modules(:all))

      assert length(defaults) == preload_count
    end

    test ":core returns only the core-tagged modules" do
      core = Docs.default_uses(:core)

      assert "Std.Core" in core
      assert "Std.Equatable" in core
      assert "Std.Comparable" in core
      refute "Std.List" in core
      refute "Std.Http" in core
    end

    test "a list of groups unions their membership" do
      merged = Docs.default_uses([:core, :collections])
      assert "Std.Core" in merged
      assert "Std.List" in merged
      refute "Std.Http" in merged
    end
  end

  describe "locate_source/2" do
    @tag :tmp_dir
    test "resolves Std.List to lib/std/list.cure when running from the repo root" do
      # This test only runs meaningfully from the Cure repo checkout where
      # `lib/std/list.cure` exists; skip gracefully otherwise.
      if File.regular?(Path.join(["lib", "std", "list.cure"])) do
        assert {:ok, path} = Docs.locate_source("Std.List", %{loaded: []})
        assert Path.basename(path) == "list.cure"
      else
        :ok
      end
    end

    test "returns :not_found for a non-existent module" do
      assert :not_found = Docs.locate_source("No.Such.Module.Ever", %{loaded: []})
    end

    test "resolves a module placed in :stdlib_source_dir (simulated release layout)" do
      source = Path.join(["lib", "std", "list.cure"])

      if File.regular?(source) do
        tmp = Path.join(System.tmp_dir!(), "cure_docs_test_#{System.unique_integer([:positive])}")
        File.mkdir_p!(tmp)
        File.cp!(source, Path.join(tmp, "list.cure"))

        previous = Application.get_env(:cure, :stdlib_source_dir)

        try do
          Application.put_env(:cure, :stdlib_source_dir, tmp)

          assert {:ok, path} = Docs.locate_source("Std.List", %{loaded: []})
          assert Path.dirname(path) == tmp
          assert Path.basename(path) == "list.cure"
        after
          case previous do
            nil -> Application.delete_env(:cure, :stdlib_source_dir)
            value -> Application.put_env(:cure, :stdlib_source_dir, value)
          end

          File.rm_rf!(tmp)
        end
      else
        :ok
      end
    end
  end

  describe "render/2" do
    test "produces no crash for a real stdlib module" do
      if File.regular?(Path.join(["lib", "std", "list.cure"])) do
        state = fake_state()
        assert :ok = Docs.render("Std.List", state)
        assert :ok = Docs.render("Cure.Std.List", state)
        assert :ok = Docs.render("Std.List.map", state)
      else
        :ok
      end
    end

    test "emits a friendly message for unknown modules" do
      state = fake_state()
      assert :ok = Docs.render("No.Such.Module", state)
    end

    test "rejects bare lowercase names with a parse error" do
      state = fake_state()
      assert :ok = Docs.render("map", state)
    end

    test "source parse failures use the structured diagnostic renderer" do
      tmp = Path.join(System.tmp_dir!(), "cure_docs_bad_#{System.unique_integer([:positive])}")
      File.mkdir_p!(tmp)
      File.write!(Path.join(tmp, "bad.cure"), "mod Bad\n  fn broken(] -> Int = 1\nend\n")

      previous = Application.get_env(:cure, :stdlib_source_dir)

      try do
        Application.put_env(:cure, :stdlib_source_dir, tmp)

        output =
          ExUnit.CaptureIO.capture_io(:stderr, fn ->
            Docs.render("Std.Bad", Map.put(fake_state(), :error_device, :stderr))
          end)

        assert output =~ "[E094]"
        assert output =~ "bad.cure"
        assert output =~ "fn broken(] -> Int = 1"
        assert output =~ "^"
        assert length(Regex.scan(~r/-- .* \[E094\]/, output)) == 1
        refute output =~ "{:unexpected_token"
      after
        if is_nil(previous),
          do: Application.delete_env(:cure, :stdlib_source_dir),
          else: Application.put_env(:cure, :stdlib_source_dir, previous)

        File.rm_rf!(tmp)
      end
    end
  end

  defp fake_state do
    %{theme: Theme.for_name(:mono), loaded: []}
  end
end
