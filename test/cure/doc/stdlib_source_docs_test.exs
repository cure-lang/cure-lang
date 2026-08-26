defmodule Cure.Doc.StdlibSourceDocsTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Doc.Extractor

  @stdlib Path.expand("../../../lib/std", __DIR__)

  test "every stdlib module has source-owned module documentation" do
    missing =
      @stdlib
      |> Path.join("*.cure")
      |> Path.wildcard()
      |> Enum.sort()
      |> Enum.flat_map(fn file ->
        {:ok, source} = File.read(file)
        {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
        {:ok, ast} = Parser.parse(tokens, file: file, emit_events: false)
        doc = Extractor.extract(ast)

        if is_binary(doc.module_doc) and String.trim(doc.module_doc) != "" do
          []
        else
          [Path.basename(file)]
        end
      end)

    assert missing == [], "stdlib modules without source documentation: #{inspect(missing)}"
  end

  test "the static stdlib renderer consumes the extracted source docs" do
    modules =
      @stdlib
      |> Path.join("*.cure")
      |> Path.wildcard()
      |> Enum.sort()
      |> Enum.map(fn file ->
        {:ok, source} = File.read(file)
        {:ok, tokens} = Lexer.tokenize(source, file: file, emit_events: false)
        {:ok, ast} = Parser.parse(tokens, file: file, emit_events: false)
        Extractor.extract(ast)
      end)

    output = Path.join(System.tmp_dir!(), "cure-stdlib-docs-#{System.unique_integer([:positive])}")

    on_exit(fn -> File.rm_rf(output) end)

    assert :ok = Cure.Doc.HTMLGenerator.generate(modules, output, title: "Cure stdlib")
    assert File.regular?(Path.join(output, "index.html"))
    assert File.regular?(Path.join(output, "std_core.html"))
    assert File.read!(Path.join(output, "std_core.html")) =~ "Identity, composition"

    assert File.read!(Path.join(output, "std_proof_lineararithmetic.html")) =~
             "Executable affine syntax"

    assert File.read!(Path.join(output, "std_decision.html")) =~ "Decidable propositions"
    assert File.read!(Path.join(output, "std_equivalent.html")) =~ "Propositional equality"
  end
end
