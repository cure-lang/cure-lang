defmodule Mix.Tasks.Cure.RewriteTest do
  use ExUnit.Case, async: false

  setup do
    previous_shell = Mix.shell()
    Mix.shell(Mix.Shell.IO)

    dir = Path.join(System.tmp_dir!(), "cure_rewrite_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)

    on_exit(fn ->
      Mix.shell(previous_shell)
      Mix.Task.reenable("cure.rewrite")
      File.rm_rf!(dir)
    end)

    {:ok, dir: dir}
  end

  test "a conditional embedded in a call-argument list is left unrewritten (paren-context), not turned into unparseable output" do
    src = "mod M\nfn g(x: Int) -> Int = h(if x > 0 then 1 else 2)\n"

    ast =
      Cure.Compiler.Lexer.tokenize(src, file: "t.cure", emit_events: false)
      |> then(fn {:ok, toks} -> Cure.Compiler.Parser.parse(toks, file: "t.cure", emit_events: false) end)
      |> then(fn {:ok, ast} -> ast end)

    new_ast = Mix.Tasks.Cure.Rewrite.rewrite(ast)
    out = Cure.Compiler.Printer.quoted_to_string(new_ast)

    refute out =~ "pickup"
    # Full reparse (lex AND parse), not just tokenize -- tokenizing alone does
    # not prove the output is syntactically valid.
    assert {:ok, toks2} = Cure.Compiler.Lexer.tokenize(out, file: "t.cure", emit_events: false)
    assert {:ok, _ast2} = Cure.Compiler.Parser.parse(toks2, file: "t.cure", emit_events: false)
  end

  test "missing files render the shared operational diagnostic without fabricated source", %{dir: dir} do
    path = Path.join(dir, "missing.cure")
    Mix.Task.reenable("cure.rewrite")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert :ok = Mix.Task.run("cure.rewrite", [path])
      end)

    assert output =~ "COULD NOT READ FILE [E095]"
    assert output =~ path
    refute output =~ "1 |"
    refute output =~ "{:file_read_error"
  end

  test "syntax failures retain source and caret context through the shared sink", %{dir: dir} do
    path = Path.join(dir, "broken.cure")
    File.write!(path, "mod Broken\n  fn run() -> Int =\nend\n")
    Mix.Task.reenable("cure.rewrite")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert :ok = Mix.Task.run("cure.rewrite", [path])
      end)

    assert output =~ "FUNCTION BODY IS MISSING [E094]"
    assert output =~ "This function declaration ends after `=`"
    assert output =~ "2 |   fn run() -> Int ="
    assert output =~ "^ write the function body after this `=`"
    assert output =~ "Hint: Write an expression after `=`"
    refute output =~ "{:unexpected"
  end

  test "unknown options fail as E099 before filesystem processing", %{dir: dir} do
    path = Path.join(dir, "untouched.cure")
    File.write!(path, "mod Untouched\nend\n")
    Mix.Task.reenable("cure.rewrite")

    output =
      ExUnit.CaptureIO.capture_io(:stderr, fn ->
        assert catch_exit(Mix.Task.run("cure.rewrite", ["--unknown", path])) == {:shutdown, 1}
      end)

    assert output =~ "INVALID COMMAND USAGE [E099]"
    assert output =~ "Invalid options for mix cure.rewrite"
    refute output =~ "file(s) rewritten"
  end
end
