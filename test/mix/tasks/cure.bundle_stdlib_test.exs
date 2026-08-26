defmodule Mix.Tasks.Cure.BundleStdlibTest do
  use ExUnit.Case, async: true

  alias Mix.Tasks.Cure.BundleStdlib

  describe "bundle/2" do
    test "copies every .cure file from src to dst" do
      src = make_tmp!()
      dst = make_tmp!()

      write_cure!(src, "list.cure", "mod List\n")
      write_cure!(src, "map.cure", "mod Map\n")

      assert {:ok, %{copied: 2, skipped: 0}} = BundleStdlib.bundle(src, dst)

      assert File.read!(Path.join(dst, "list.cure")) == "mod List\n"
      assert File.read!(Path.join(dst, "map.cure")) == "mod Map\n"
    after
      cleanup_tmps()
    end

    test "is a no-op when the source directory does not exist" do
      src = Path.join(System.tmp_dir!(), "cure_bundle_test_missing_#{unique()}")
      dst = make_tmp!()

      assert {:ok, %{copied: 0, skipped: 0}} = BundleStdlib.bundle(src, dst)
      assert File.ls!(dst) == []
    after
      cleanup_tmps()
    end

    test "creates the destination directory when it does not exist" do
      src = make_tmp!()
      dst = Path.join(System.tmp_dir!(), "cure_bundle_dst_#{unique()}")
      write_cure!(src, "core.cure", "mod Core\n")

      assert {:ok, %{copied: 1}} = BundleStdlib.bundle(src, dst)
      assert File.dir?(dst)
      assert Path.basename(Path.join(dst, "core.cure")) == "core.cure"
    after
      cleanup_tmps()
    end

    test "skips files whose destination is up to date" do
      src = make_tmp!()
      dst = make_tmp!()
      write_cure!(src, "list.cure", "mod List\n")

      # First run copies.
      assert {:ok, %{copied: 1, skipped: 0}} = BundleStdlib.bundle(src, dst)

      # Force the destination to be strictly newer than the source so
      # the mtime gate says "skip".
      bump_mtime!(Path.join(dst, "list.cure"), 5)

      assert {:ok, %{copied: 0, skipped: 1}} = BundleStdlib.bundle(src, dst)
    after
      cleanup_tmps()
    end

    test "re-copies files when the source has been updated" do
      src = make_tmp!()
      dst = make_tmp!()
      write_cure!(src, "list.cure", "mod List\n")

      assert {:ok, %{copied: 1}} = BundleStdlib.bundle(src, dst)

      # Rewrite the source *and* bump its mtime into the future so the
      # gate trips regardless of filesystem timestamp granularity.
      File.write!(Path.join(src, "list.cure"), "mod List.Updated\n")
      bump_mtime!(Path.join(src, "list.cure"), 10)

      assert {:ok, %{copied: 1, skipped: 0}} = BundleStdlib.bundle(src, dst)
      assert File.read!(Path.join(dst, "list.cure")) == "mod List.Updated\n"
    after
      cleanup_tmps()
    end

    test "ignores non-`.cure` files sitting in the source directory" do
      src = make_tmp!()
      dst = make_tmp!()
      write_cure!(src, "list.cure", "mod List\n")
      File.write!(Path.join(src, "README.md"), "# not Cure source")

      assert {:ok, %{copied: 1}} = BundleStdlib.bundle(src, dst)
      refute File.exists?(Path.join(dst, "README.md"))
    after
      cleanup_tmps()
    end

    test "removes bundled Cure sources that no longer belong to the stdlib" do
      src = make_tmp!()
      dst = make_tmp!()
      write_cure!(src, "otp.cure", "mod Std.Otp\n")
      write_cure!(dst, "otp.cure", "stale\n")
      write_cure!(dst, "removed_proof.cure", "mod Std.Removed.Proof\n")
      File.write!(Path.join(dst, "README.md"), "keep me")

      assert {:ok, counts} = BundleStdlib.bundle(src, dst)
      assert counts.copied + counts.skipped == 1
      refute File.exists?(Path.join(dst, "removed_proof.cure"))
      assert File.exists?(Path.join(dst, "README.md"))
    after
      cleanup_tmps()
    end
  end

  describe "should_copy?/2" do
    test "returns true when the destination does not exist" do
      src = make_tmp!()
      write_cure!(src, "list.cure", "mod List\n")

      assert BundleStdlib.should_copy?(
               Path.join(src, "list.cure"),
               Path.join(src, "missing_dst.cure")
             )
    after
      cleanup_tmps()
    end

    test "returns false when the source does not exist" do
      refute BundleStdlib.should_copy?(
               "/nonexistent/src.cure",
               "/nonexistent/dst.cure"
             )
    end
  end

  # ---------------------------------------------------------------------------

  defp make_tmp! do
    path = Path.join(System.tmp_dir!(), "cure_bundle_test_#{unique()}")
    File.mkdir_p!(path)
    Process.put(:cleanup, [path | Process.get(:cleanup, [])])
    path
  end

  defp cleanup_tmps do
    Process.get(:cleanup, []) |> Enum.each(&File.rm_rf!/1)
    Process.put(:cleanup, [])
  end

  defp write_cure!(dir, name, contents) do
    File.write!(Path.join(dir, name), contents)
  end

  # Bumps the given file's mtime by `offset_seconds` into the future.
  # `File.touch!/2` with a posix time is portable across Linux/macOS.
  defp bump_mtime!(path, offset_seconds) do
    {:ok, %File.Stat{mtime: mtime}} = File.stat(path, time: :posix)
    File.touch!(path, mtime + offset_seconds)
  end

  defp unique, do: System.unique_integer([:positive])
end
