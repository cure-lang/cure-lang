defmodule Cure.REPL.CompleterTest do
  # async: false -- the `:load path completion` block changes cwd to a
  # scratch directory so it can assert against a known filesystem layout.
  use ExUnit.Case, async: false

  alias Cure.REPL.Completer

  describe "meta-command completion" do
    test "unique match extends the token" do
      assert {:unique, ":history"} = Completer.complete(":histo", 6)
    end

    test "multiple matches return partial prefix" do
      result = Completer.complete(":h", 2)
      assert match?({:partial, _, _}, result)
      {:partial, common, cands} = result
      assert String.starts_with?(common, ":h")
      assert ":help" in cands
      assert ":history" in cands
      assert ":h" in cands
    end

    test "no match returns :none" do
      assert :none = Completer.complete(":xyzxyz", 7)
    end
  end

  describe "keyword fallback" do
    test "partial Cure keyword completes uniquely" do
      assert {:unique, "match"} = Completer.complete("matc", 4)
    end

    test "offers canonical declaration and conditional spellings" do
      assert {:unique, "interface"} = Completer.complete("interf", 6)
      assert {:unique, "implementation"} = Completer.complete("implementa", 10)
      assert {:unique, "pickup"} = Completer.complete("pick", 4)
      assert :none = Completer.complete("proto", 5)
    end
  end

  describe ":load path completion" do
    setup do
      root = Path.join(System.tmp_dir!(), "cure-completer-#{System.unique_integer([:positive])}")
      File.mkdir_p!(Path.join(root, "examples"))
      File.write!(Path.join([root, "examples", "let_destructuring.cure"]), "")
      File.write!(Path.join([root, "examples", "match_showcase.cure"]), "")
      File.mkdir_p!(Path.join(root, "extra"))
      File.write!(Path.join(root, "readme.md"), "")

      cwd = File.cwd!()
      File.cd!(root)

      on_exit(fn ->
        File.cd!(cwd)
        File.rm_rf!(root)
      end)

      %{root: root}
    end

    test "nested path keeps the user's directory prefix on a unique match" do
      buffer = ":load examples/let"

      assert {:unique, ":load examples/let_destructuring.cure"} =
               Completer.complete(buffer, String.length(buffer))
    end

    test "nested path surfaces prefixed candidates on :partial" do
      buffer = ":load examples/"
      result = Completer.complete(buffer, String.length(buffer))
      assert {:partial, common, cands} = result
      assert common == "examples/" or String.starts_with?(common, "examples/")
      assert "examples/let_destructuring.cure" in cands
      assert "examples/match_showcase.cure" in cands
    end

    test "bare token in cwd completes directories with a trailing slash" do
      buffer = ":load exa"

      assert {:unique, ":load examples/"} =
               Completer.complete(buffer, String.length(buffer))
    end

    test "cwd-relative `./` prefix is preserved" do
      buffer = ":load ./exa"

      assert {:unique, ":load ./examples/"} =
               Completer.complete(buffer, String.length(buffer))
    end

    test "multiple top-level candidates share the correct common prefix" do
      buffer = ":load ex"
      result = Completer.complete(buffer, String.length(buffer))
      assert {:partial, "ex", cands} = result
      assert "examples/" in cands
      assert "extra/" in cands
    end
  end
end
