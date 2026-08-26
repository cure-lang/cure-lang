defmodule Cure do
  @moduledoc """
  Cure -- dependently-typed programming language for the BEAM virtual machine
  with first-class finite state machines and Z3-assisted guard analysis.

  Cure compiles `.cure` source files to BEAM bytecode through the following pipeline:

      .cure source
        |  Cure.Compiler.Lexer        (tokenization)
        v
      Token stream
        |  Cure.Compiler.Parser       (MetaAST generation)
        v
      MetaAST (Metastatic 3-tuples)
        |  Cure.Elab.Program          (dependent elaboration)
        v
      Checked Cure.Core
        |  Cure.Core.Kernel           (validation)
        |  Cure.Elab.Erase            (proof/index erasure)
        |  Cure.Elab.Emit             (Erlang abstract forms)
        v
      BEAM bytecode

  Every pipeline stage emits structured events through `Cure.Pipeline.Events`,
  enabling external tools (LSP, profilers, IDE plugins) to observe and react
  to compilation in real time.

  ## Internal Representation

  Cure uses [Metastatic](https://hexdocs.pm/metastatic)'s MetaAST 3-tuple
  format as its internal AST representation:

      {type_atom, keyword_meta, children_or_value}

  This enables interoperability with Metastatic's cross-language analysis
  tools and provides a well-defined, layered AST structure.
  """

  alias Cure.Compiler.{Lexer, Parser}

  # Register the top-level `mix.exs` as an external resource so the
  # compiler re-evaluates this module whenever the version (or any
  # other project attribute) changes in `mix.exs`. Without this, a
  # bare `mix compile` after a version bump leaves the old value
  # baked into `Cure.version/0` until `lib/cure.ex` itself is touched.
  @external_resource Path.expand("../mix.exs", __DIR__)
  @version Cure.MixProject.project()[:version]

  @doc """
  Returns the current Cure version.

  The value is resolved at compile time from the top-level `mix.exs`
  of the Cure project, so it always tracks the `@version` declared
  there.
  """
  @spec version :: String.t()
  def version, do: @version

  @doc """
  Parse a Cure source string into its MetaAST representation.

  Runs the full lexer-then-parser pipeline and returns the resulting
  `{type, meta, children_or_value}` tree.

  ## Options

  - `:file` -- filename for source metadata (default: `"nofile"`)
  - `:emit_events` -- whether to emit pipeline events (default: `false`)

  ## Examples

      iex> {:ok, {:literal, meta, 42}} = Cure.quote("42")
      iex> Keyword.fetch!(meta, :subtype)
      :integer

      iex> {:ok, {:binary_op, meta, _}} = Cure.quote("x + 1")
      iex> Keyword.fetch!(meta, :operator)
      :+
  """
  @spec quote(String.t(), keyword()) :: {:ok, Parser.ast()} | {:error, term()}
  def quote(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, false)
    lex_opts = parse_opts = [file: file, emit_events: emit?]

    with {:ok, tokens} <- Lexer.tokenize(source, lex_opts),
         do: Parser.parse(tokens, parse_opts)
  end

  @doc """
  Convert a MetaAST tree back into Cure source code.

  This is the inverse of `quote/2`. Given a well-formed MetaAST, it produces
  a Cure source string that, when re-quoted, yields an equivalent AST.

  ## Options

  - `:indent` -- base indentation string (default: `"  "` -- two spaces)

  ## Examples

      iex> {:ok, ast} = Cure.quote("let x = 42")
      iex> Cure.quoted_to_string(ast)
      "let x = 42"
  """
  @spec quoted_to_string(Parser.ast(), keyword()) :: String.t()
  defdelegate quoted_to_string(ast, opts \\ []), to: Cure.Compiler.Printer
end
