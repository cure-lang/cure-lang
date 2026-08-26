defmodule Cure.Doc.Snippets do
  @moduledoc """
  Discovers and compiles `cure` fenced code blocks in Markdown files and Cure
  docstrings.

  A fence is checked when its info string starts with the complete word
  `cure`; for example, both `` ```cure `` and
  `` ```cure path=example.cure `` are checked. The source may be a complete
  module, a group of declarations, or an expression. Declaration and expression
  snippets are placed in a uniquely named synthetic module.

  A fence may declare its expected outcome with one diagnostic tag: an `E` code
  for a snippet the compiler must reject, or a `W` code for a snippet that must
  compile while emitting that warning. An untagged fence must compile with no
  warnings at all. There is no tag that opts a `cure` fence out of checking —
  an incomplete sketch belongs in a plain `text` fence, which is never
  extracted.

  Repository checks use tracked and untracked, non-ignored Markdown and Cure
  files. Historical release notes and design archives are deliberately outside
  the executable documentation contract; user-facing docs and all Cure
  docstrings remain covered.
  """

  @enforce_keys [:path, :line, :code, :info]
  defstruct [:path, :line, :code, :info]

  @type t :: %__MODULE__{
          path: Path.t(),
          line: pos_integer(),
          code: String.t(),
          info: String.t()
        }

  # Every word that can head a top-level declaration. A head missing from this
  # list is read as the start of an expression, so the fence is wrapped in
  # `fn snippet() =` and then fails on the wrapper's shape rather than on
  # anything the page wrote. `proto`/`impl` are deliberately absent: they are
  # retired spellings that emit a migration warning and do not reach codegen.
  @declaration_starts ~w[
    @
    data
    effect
    fn
    implementation
    interface
    local
    macro
    opaque
    precedencegroup
    primitive
    rec
    type
    typealias
    use
  ]

  @doc "Return every tracked or untracked, non-ignored Markdown file below `root`."
  @spec markdown_files(Path.t()) :: [Path.t()]
  def markdown_files(root \\ File.cwd!()) do
    repository_files(root, "*.md")
  end

  @doc "Return every tracked or untracked, non-ignored Cure file below `root`."
  @spec cure_files(Path.t()) :: [Path.t()]
  def cure_files(root \\ File.cwd!()) do
    repository_files(root, "*.cure")
  end

  defp repository_files(root, pattern) do
    case System.cmd(
           "git",
           ["ls-files", "--cached", "--others", "--exclude-standard", "-z", "--", pattern],
           cd: root
         ) do
      {output, 0} ->
        output
        |> String.split(<<0>>, trim: true)
        |> Enum.map(&Path.join(root, &1))
        |> Enum.filter(&File.regular?/1)
        |> Enum.reject(&documentation_archive?/1)
        |> Enum.sort()

      {_output, _status} ->
        Path.wildcard(Path.join(root, "**/#{pattern}"))
        |> Enum.reject(&(excluded_path?(&1) or documentation_archive?(&1)))
        |> Enum.sort()
    end
  end

  # Design notes, release history, and generated reports intentionally contain
  # illustrative or historical Cure syntax. They are not API documentation and
  # must not silently become part of the executable documentation contract.
  # Authoritative docs and all Cure source docstrings remain covered.
  defp documentation_archive?(path) do
    normalized = Path.expand(path)

    String.contains?(normalized, "/docs/superpowers/") or
      String.contains?(normalized, "/site/priv/posts/") or
      String.contains?(normalized, "/blog/") or
      Path.basename(normalized) in [
        "CHANGELOG.md",
        "RELEASE.md",
        "RELEASE-0.18.0.md",
        "ROADMAP-0.34.md",
        "DEPENDENT_KERNEL_PEERNESS_ROADMAP.md",
        "DEPENDENT_TYPE_SLICES.md",
        "STDLIB_DEPENDENT_CLAIMS_AUDIT.md",
        "AUTOPILOT-REPORT-anonymous-adts.md"
      ] or
      normalized in [Path.expand("docs/STDLIB.md"), Path.expand("docs/DOC.md")]
  end

  @doc "Extract checked Cure fences from one Markdown file."
  @spec extract_file(Path.t()) :: {:ok, [t()]} | {:error, File.posix()}
  def extract_file(path) do
    with {:ok, markdown} <- File.read(path) do
      {:ok, extract(markdown, path)}
    end
  end

  @doc "Extract checked Cure fences from Cure docstrings in one source file."
  @spec extract_cure_file(Path.t()) :: {:ok, [t()]} | {:error, File.posix()}
  def extract_cure_file(path) do
    with {:ok, source} <- File.read(path) do
      {:ok, extract_cure(source, path)}
    end
  end

  @doc "Extract checked Cure fences from doc comments in Cure source."
  @spec extract_cure(String.t(), Path.t()) :: [t()]
  def extract_cure(source, path \\ "nofile.cure") when is_binary(source) do
    source
    |> docstring_markdown()
    |> extract(path)
  end

  @doc "Extract checked Cure fences from Markdown source."
  @spec extract(String.t(), Path.t()) :: [t()]
  def extract(markdown, path \\ "nofile.md") when is_binary(markdown) do
    markdown
    |> String.split("\n", trim: false)
    |> Enum.with_index(1)
    |> extract_lines(path, nil, [])
    |> Enum.reverse()
  end

  @doc """
  Return the whitespace/comma-separated tags following `cure`.

  Attribute tokens such as `path=demo.cure` are metadata, not tags.
  """
  @spec tags(t() | String.t()) :: MapSet.t(String.t())
  def tags(%__MODULE__{info: info}), do: tags(info)

  def tags(info) when is_binary(info) do
    info
    |> String.split(~r/[\s,]+/, trim: true)
    |> Enum.drop(1)
    |> Enum.reject(&String.contains?(&1, "="))
    |> MapSet.new()
  end

  @doc "Return whether a snippet carries `tag` in its fence info string."
  @spec tagged?(t(), String.t()) :: boolean()
  def tagged?(%__MODULE__{} = snippet, tag), do: MapSet.member?(tags(snippet), tag)

  @doc """
  Return the single expected diagnostic code declared by the fence.

  An `E` code declares a snippet the compiler must reject. A `W` code declares
  a snippet that must compile *and* emit that warning; some documented
  constructs have no warning-free form, and silently dropping the warning would
  be a weaker claim than pinning it.
  """
  @spec expected_diagnostic(t()) :: nil | {:ok, String.t()} | {:error, [String.t()]}
  def expected_diagnostic(%__MODULE__{} = snippet) do
    codes =
      snippet
      |> tags()
      |> Enum.filter(&Regex.match?(~r/^[EW]\d{3}$/, &1))
      |> Enum.sort()

    case codes do
      [] -> nil
      [code] -> {:ok, code}
      _ -> {:error, codes}
    end
  end

  @doc """
  Compile a snippet.

  `support` is a declaration-only Cure source appended inside synthetic
  modules. Appending it keeps diagnostics for the authored snippet aligned with
  the Markdown line numbers.
  """
  @spec compile(t(), keyword()) :: {:ok, module(), [term()]} | {:error, term()}
  def compile(%__MODULE__{} = snippet, opts \\ []) do
    support = Keyword.get(opts, :support, "")
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/doc_snippets")
    source_roots = Keyword.get(opts, :source_roots, [])
    stdlib_ebin = Keyword.get(opts, :stdlib_ebin)
    source = source(snippet, support)

    with :ok <- prepare_stdlib(stdlib_ebin, source_roots) do
      Cure.Compiler.compile_string(source,
        file: snippet.path,
        output_dir: output_dir,
        source_roots: source_roots,
        emit_events: false
      )
    end
  end

  defp prepare_stdlib(stdlib_ebin, source_roots) when is_binary(stdlib_ebin) do
    # Keep the resolver pointed at the repository stdlib when snippets are
    # compiled outside Mix (the docs task and editor integrations both do
    # this).  A loaded BEAM alone is not enough for source-backed `use`
    # resolution.
    if source_roots != [] do
      # CURE_LIB names the compiled ebin directory (its sibling `../std`
      # is used for source resolution), not the source checkout directory.
      System.put_env("CURE_LIB", stdlib_ebin)
    end

    if File.dir?(stdlib_ebin) do
      :code.add_patha(String.to_charlist(stdlib_ebin))
    end

    with :ok <-
           Cure.Stdlib.Preload.preload(
             kind: :all,
             stdlib_ebin: stdlib_ebin,
             source_jit: false
           ) do
      case Enum.find(source_roots, &(Path.basename(&1) == "std")) do
        nil -> :ok
        source_dir -> Application.put_env(:cure, :stdlib_source_dir, source_dir)
      end
    end
  end

  defp prepare_stdlib(_stdlib_ebin, _source_roots), do: :ok

  @doc "Build the line-aligned Cure compilation unit for a snippet."
  @spec source(t(), String.t()) :: String.t()
  def source(%__MODULE__{} = snippet, support \\ "") do
    code = String.trim_trailing(snippet.code)

    if complete_module?(code) do
      pad_to_line(code, snippet.line)
    else
      module = synthetic_module(snippet)

      case snippet_kind(snippet.info, code) do
        :declarations ->
          prefix = pad_to_line("mod #{module}", max(snippet.line - 1, 1))
          prefix <> "\n" <> indent(code) <> append_support(support)

        :expression ->
          expression_source(module, code, snippet.line, support)
      end
    end
  end

  defp expression_source(module, code, line, support) do
    units =
      code
      |> String.split("\n")
      |> Enum.reject(&(String.trim(&1) == "" or String.starts_with?(String.trim(&1), "#")))

    if length(units) > 1 and Enum.all?(units, &(not String.starts_with?(&1, " "))) and
         not Enum.any?(units, &binding?/1) do
      prefix = pad_to_line("mod #{module}", max(line - 1, 1))

      functions =
        units
        |> Enum.with_index(1)
        |> Enum.map_join("\n", fn {expression, index} ->
          "  fn snippet_#{index}() = #{expression}"
        end)

      prefix <> "\n" <> functions <> append_support(support)
    else
      # One `fn` per line, the branch above, is for a fence listing several
      # independent example expressions. A `let` rules that reading out: it has
      # no value without the body that follows it, so a fence containing one is
      # a single block that happens to be written flush left, and splitting it
      # strands every binding in a function with no body.
      prefix = pad_to_line("mod #{module}\n  fn snippet() =", max(line - 2, 1))
      prefix <> "\n" <> indent(code, 4) <> append_support(support)
    end
  end

  defp binding?(line), do: Regex.match?(~r/^let\s/, line)

  defp extract_lines([], _path, nil, acc), do: acc
  defp extract_lines([], path, open, _acc), do: raise("unclosed Markdown fence in #{path}:#{open.line - 1}")

  defp extract_lines([{line, number} | rest], path, nil, acc) do
    case opening_fence(line) do
      {:ok, marker, info} ->
        open = %{marker: marker, info: info, line: number + 1, body: []}
        extract_lines(rest, path, open, acc)

      :error ->
        extract_lines(rest, path, nil, acc)
    end
  end

  defp extract_lines([{line, _number} | rest], path, open, acc) do
    if closing_fence?(line, open.marker) do
      acc =
        if cure_info?(open.info) do
          [
            %__MODULE__{
              path: path,
              line: open.line,
              code: open.body |> Enum.reverse() |> Enum.join("\n"),
              info: open.info
            }
            | acc
          ]
        else
          acc
        end

      extract_lines(rest, path, nil, acc)
    else
      extract_lines(rest, path, %{open | body: [line | open.body]}, acc)
    end
  end

  defp opening_fence(line) do
    case Regex.run(~r/^\s{0,3}(`{3,}|~{3,})(.*)$/, line) do
      [_, marker, info] -> {:ok, marker, String.trim(info)}
      _ -> :error
    end
  end

  defp closing_fence?(line, marker) do
    char = String.first(marker)
    min = String.length(marker)
    Regex.match?(~r/^\s{0,3}#{Regex.escape(char)}{#{min},}\s*$/, line)
  end

  defp cure_info?(info), do: Regex.match?(~r/^cure(?:\s|,|$)/, info)

  defp complete_module?(code) do
    Regex.match?(~r/^\s*(?:@\w+(?:\([^)]*\))?\s+)*mod\s+/, code) or whole_unit?(code)
  end

  # A fence that opens with `use` and then declares something at the top level —
  # a `mod`, or one of the concurrency containers, which are top-level forms in
  # their own right — is already a complete compilation unit. Wrapping it in the
  # synthetic `mod DocSnippet_…` would nest those declarations one level down,
  # and a nested module cannot be named by its siblings: every qualified call
  # between them fails with `unknown_global`, which is exactly the shape a doc
  # page uses to show client code driving an `fsm`.
  defp whole_unit?(code) do
    Regex.match?(~r/\A\s*use\s+\S/, code) and Regex.match?(~r/^(?:mod|fsm|actor|sup|app)\s+\S/m, code)
  end

  defp snippet_kind(info, code) do
    cond do
      MapSet.member?(tags(info), "expr") -> :expression
      not MapSet.disjoint?(tags(info), MapSet.new(["declaration", "declarations"])) -> :declarations
      declaration_source?(code) -> :declarations
      true -> :expression
    end
  end

  defp declaration_source?(code) do
    first =
      code
      |> String.split("\n")
      |> Enum.map(&String.trim/1)
      |> Enum.reject(&(&1 == "" or String.starts_with?(&1, "#")))
      |> List.first()

    case first do
      nil -> true
      "@" <> _attribute -> true
      line -> Enum.any?(@declaration_starts, &(line == &1 or String.starts_with?(line, &1 <> " ")))
    end
  end

  defp synthetic_module(snippet) do
    digest =
      :crypto.hash(:sha256, "#{snippet.path}:#{snippet.line}:#{snippet.code}")
      |> Base.encode16(case: :lower)
      |> binary_part(0, 16)

    "DocSnippet_#{digest}"
  end

  defp pad_to_line(source, line) when line <= 1, do: source
  defp pad_to_line(source, line), do: String.duplicate("\n", line - 1) <> source

  defp indent(source, spaces \\ 2) do
    prefix = String.duplicate(" ", spaces)

    source
    |> String.split("\n", trim: false)
    |> Enum.map_join("\n", fn
      "" -> ""
      line -> prefix <> line
    end)
  end

  defp append_support(""), do: "\n"
  defp append_support(support), do: "\n\n" <> indent(String.trim(support)) <> "\n"

  defp excluded_path?(path) do
    Enum.any?(["/.git/", "/_build/", "/deps/", "/site/deps/", "/doc/"], &String.contains?(path, &1))
  end

  # Turn source doc comments into a Markdown view while retaining one output
  # line per source line. This lets diagnostics point at the original `.cure`
  # location after a snippet is wrapped in a synthetic module.
  defp docstring_markdown(source) do
    {lines, _in_fence} =
      source
      |> String.split("\n", trim: false)
      |> Enum.map_reduce(nil, fn line, in_fence ->
        {rendered, next_in_fence} = docstring_line(line, in_fence)
        {rendered, next_in_fence}
      end)

    Enum.join(lines, "\n")
  end

  defp docstring_line(line, indent) when is_binary(indent) do
    if String.trim(line) == "###" do
      {"", nil}
    else
      {String.replace_prefix(line, indent, ""), indent}
    end
  end

  defp docstring_line(line, nil) do
    case Regex.run(~r/^\s*##(?!#)(?: ?)(.*)$/, line) do
      [_, body] -> {body, nil}
      _ -> {"", doc_fence_indent(line)}
    end
  end

  defp doc_fence_indent(line) do
    case Regex.run(~r/^(\s*)###\s*$/, line) do
      [_, indent] -> indent
      _ -> nil
    end
  end
end
