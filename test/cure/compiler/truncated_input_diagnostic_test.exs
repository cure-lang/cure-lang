defmodule Cure.Compiler.TruncatedInputDiagnosticTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Parser.FixityScan
  alias Cure.Compiler.Parser.FixityTable
  alias Cure.Compiler.SourceResolver

  # Running out of tokens is an ordinary syntax error, not a compiler crash.
  # `peek/1` past the last token synthesizes an EOF token carrying no span (the
  # lexer never authored one), so every diagnostic path that narrows the
  # observed token's span to a zero-width caret has to tolerate a missing span.
  #
  # This bites well beyond truncated user input. `harvest/4` promises never to
  # raise, and `Cure.Compiler.SourceResolver` leans on that: to resolve a module
  # by name it harvests *every* `.cure` file under the configured source roots.
  # A raise from one of those files surfaces as an unhandled FunctionClauseError
  # attributed to whichever unrelated program triggered the lookup.

  defp harvest(source), do: FixityScan.harvest_source(source, "nofile", FixityTable.new())

  test "every stdlib source can be harvested" do
    for path <- Path.wildcard("lib/std/**/*.cure") ++ Path.wildcard("lib/std_deps/regex/*.cure") do
      assert harvest(File.read!(path)), "harvest returned nothing for #{path}"
    end
  end

  test "resolving an unknown module against the stdlib source root does not raise" do
    previous = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, [Path.expand("lib/std")])

    try do
      assert SourceResolver.module_path("Doc.NoSuchModule") == :not_found
    after
      if previous, do: Process.put(:cure_source_roots, previous), else: Process.delete(:cure_source_roots)
    end
  end
end
