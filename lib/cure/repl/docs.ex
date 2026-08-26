defmodule Cure.REPL.Docs do
  @moduledoc """
  `:doc` support for the Cure REPL.

  Resolves a user-supplied target (e.g. `Cure.Std.List`, `Std.List`,
  `Std.List.map`, or just `map` when a single matching function exists)
  to the corresponding `.cure` source file, parses it, extracts the
  structured documentation via `Cure.Doc.Extractor`, and prints a
  coloured, paginator-friendly block back to the terminal.

  Source lookup walks three roots in order:

    1. `lib/std/` -- the bundled Cure standard library.
    2. Any path the user has previously loaded via `:load` -- so
       `:doc MyMod` works after `:load path/to/my_mod.cure`.
    3. Explicit `:cure_source_roots` paths configured on the REPL
       application environment.

  Parsed doc payloads are cached in the process dictionary keyed by
  `{path, mtime}`, so back-to-back `:doc` queries don't re-lex a file
  on every invocation.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Doc.Extractor
  alias Cure.Diagnostic.{Host, Sink}
  alias Cure.REPL.{Markdown, Render}
  alias Cure.Stdlib.{Paths, Preload}

  @cache_key :cure_repl_doc_cache

  @typedoc "A fully-resolved doc target."
  @type target ::
          {:module, String.t()}
          | {:function, String.t(), String.t()}

  @doc """
  Render documentation for `name` through the REPL's theme. Always
  returns `:ok`; diagnostic messages are printed via `Cure.REPL.Render`.
  """
  @spec render(String.t(), map()) :: :ok
  def render(name, state) when is_binary(name) do
    raw = String.trim(name)

    case parse_target(raw) do
      {:ok, target} ->
        render_target(target, state)

      {:error, reason} ->
        info(state, "(cannot parse `#{raw}`: #{reason})")
    end
  end

  @doc "Search documentation names available to the current REPL session."
  @spec apropos(String.t(), map()) :: :ok
  def apropos(query, state) when is_binary(query) do
    needle = query |> String.trim() |> String.downcase()

    hits =
      search_roots(state)
      |> Enum.flat_map(&Path.wildcard(Path.join(&1, "**/*.cure")))
      |> Enum.uniq()
      |> Enum.flat_map(fn path ->
        case cached_docs(path) do
          {:ok, docs} -> apropos_entries(docs)
          {:error, _} -> []
        end
      end)
      |> Enum.filter(&(needle != "" and String.contains?(String.downcase(&1), needle)))
      |> Enum.uniq()
      |> Enum.sort()

    case hits do
      [] -> info(state, "(no declarations matching `#{query}`)")
      _ -> Enum.each(hits, &Render.write_line("  " <> &1))
    end

    :ok
  end

  defp apropos_entries(docs) do
    module = heading_name(docs, "Unknown")
    functions = Enum.map(docs.functions || [], &"#{module}.#{&1.name}/#{length(&1.params)}")
    types = Enum.map(docs.types || [], &"#{module}.#{&1.name}")
    protocols = Enum.map(docs.protocols || [], &"#{module}.#{&1.name}")
    [module | functions ++ types ++ protocols]
  end

  @doc false
  # Exposed for tests: parse a raw user string into a resolved target.
  @spec parse_target(String.t()) :: {:ok, target()} | {:error, String.t()}
  def parse_target(""), do: {:error, "empty name"}

  def parse_target(raw) do
    normalized = strip_cure_prefix(raw)

    case String.split(normalized, ".") do
      [""] ->
        {:error, "empty name"}

      [only] ->
        if lowercase_start?(only) do
          {:error, "`#{only}` is not a module; qualify it as `Module.#{only}`"}
        else
          {:ok, {:module, only}}
        end

      parts ->
        last = List.last(parts)

        if lowercase_start?(last) do
          mod = parts |> Enum.drop(-1) |> Enum.join(".")
          {:ok, {:function, mod, last}}
        else
          {:ok, {:module, Enum.join(parts, ".")}}
        end
    end
  end

  @doc false
  # Exposed for tests: locate the on-disk source file backing `module_name`.
  @spec locate_source(String.t(), map()) :: {:ok, String.t()} | :not_found
  def locate_source(module_name, state) do
    search_roots(state)
    |> Enum.find_value(:not_found, fn root ->
      case find_in_root(root, module_name) do
        {:ok, _} = hit -> hit
        :not_found -> nil
      end
    end)
  end

  # ==========================================================================
  # Rendering
  # ==========================================================================

  defp render_target({:module, mod_name}, state) do
    case load_docs(mod_name, state) do
      {:ok, %{} = docs, path} ->
        render_module(docs, path, state)

      :not_found ->
        info(state, "(no documentation source found for `#{mod_name}`)")

      {:error, error} ->
        render_extract_error(state, mod_name, error)
    end
  end

  defp render_target({:function, mod_name, fn_name}, state) do
    case load_docs(mod_name, state) do
      {:ok, %{} = docs, _path} ->
        matches = Enum.filter(docs.functions || [], &(&1.name == fn_name))

        case matches do
          [] ->
            info(state, "(no function `#{fn_name}` in `#{mod_name}`)")

          fns ->
            heading = "#{heading_name(docs, mod_name)}.#{fn_name}"
            Render.write_line(with_style(state, :underline, heading))

            Enum.each(fns, fn fn_doc ->
              Render.write_line("")
              render_function_block(fn_doc, state)
            end)
        end

      :not_found ->
        info(state, "(no documentation source found for `#{mod_name}`)")

      {:error, error} ->
        render_extract_error(state, mod_name, error)
    end
  end

  defp render_module(%{} = docs, path, state) do
    name = heading_name(docs, "?")

    Render.write_line(with_style(state, :prompt, "## " <> name))
    Render.write_line(with_style(state, :dim, "   " <> Path.relative_to_cwd(path)))

    if is_binary(docs.module_doc) and docs.module_doc != "" do
      Render.write_line("")
      Render.write_line(Markdown.render(docs.module_doc, state.theme))
    end

    render_function_index(docs, state)
    render_type_index(docs, state)
    render_protocol_index(docs, state)
    :ok
  end

  defp render_function_index(%{functions: fns}, state) when is_list(fns) and fns != [] do
    {public, private} = Enum.split_with(fns, &(&1.visibility == :public))

    Render.write_line("")
    Render.write_line(with_style(state, :info, "Functions"))

    public
    |> Enum.sort_by(&{&1.name, length(&1.params)})
    |> Enum.each(fn fn_doc ->
      sig = format_function_signature(fn_doc)
      snippet = first_doc_line(fn_doc.doc)
      line = "  " <> with_style(state, :match, sig)
      line = if snippet == "", do: line, else: line <> "  " <> with_style(state, :dim, snippet)
      Render.write_line(line)
    end)

    if private != [] do
      Render.write_line("")
      Render.write_line(with_style(state, :dim, "(#{length(private)} local function#{pluralize(private)} hidden)"))
    end
  end

  defp render_function_index(_docs, _state), do: :ok

  defp render_type_index(%{types: types}, state) when is_list(types) and types != [] do
    Render.write_line("")
    Render.write_line(with_style(state, :info, "Types"))

    Enum.each(types, fn t ->
      Render.write_line("  " <> with_style(state, :match, t.name))

      if is_binary(t.doc) and t.doc != "" do
        Render.write_line("    " <> with_style(state, :dim, first_doc_line(t.doc)))
      end
    end)
  end

  defp render_type_index(_docs, _state), do: :ok

  defp render_protocol_index(%{protocols: protos}, state) when is_list(protos) and protos != [] do
    Render.write_line("")
    Render.write_line(with_style(state, :info, "Interfaces"))

    Enum.each(protos, fn proto ->
      Render.write_line("  " <> with_style(state, :match, proto.name))

      if is_binary(proto.doc) and proto.doc != "" do
        Render.write_line("    " <> with_style(state, :dim, first_doc_line(proto.doc)))
      end
    end)
  end

  defp render_protocol_index(_docs, _state), do: :ok

  defp render_function_block(fn_doc, state) do
    Render.write_line("  " <> with_style(state, :match, format_function_signature(fn_doc)))

    effects_line =
      case fn_doc.effects do
        [] -> nil
        effs -> "  effects: " <> Enum.join(effs, ", ")
      end

    if effects_line, do: Render.write_line(with_style(state, :dim, effects_line))

    body = if is_binary(fn_doc.doc), do: fn_doc.doc, else: ""

    if body == "" do
      Render.write_line(with_style(state, :dim, "  (no docstring)"))
    else
      body
      |> Markdown.render(state.theme)
      |> indent_lines("    ")
      |> Render.write_line()
    end
  end

  defp format_function_signature(%{name: name, params: params, return_type: ret}) do
    params_str =
      params
      |> Enum.map_join(", ", fn {pname, ptype} -> "#{pname}: #{ptype}" end)

    base = "#{name}(#{params_str})"
    if is_binary(ret) and ret != "", do: base <> " -> " <> ret, else: base
  end

  defp heading_name(%{module: m}, _fallback) when is_binary(m) and m != "Unknown", do: m
  defp heading_name(_, fallback), do: fallback

  defp first_doc_line(nil), do: ""

  defp first_doc_line(doc) when is_binary(doc) do
    doc
    |> String.split("\n", parts: 2)
    |> List.first()
    |> String.trim()
  end

  defp pluralize([_]), do: ""
  defp pluralize(_), do: "s"

  defp indent_lines(text, prefix) do
    text
    |> String.split("\n")
    |> Enum.map_join("\n", &(prefix <> &1))
  end

  # ==========================================================================
  # Source lookup + doc extraction (cached)
  # ==========================================================================

  defp load_docs(mod_name, state) do
    case locate_source(mod_name, state) do
      {:ok, path} ->
        case cached_docs(path) do
          {:ok, docs} -> {:ok, docs, path}
          {:error, _} = err -> err
        end

      :not_found ->
        :not_found
    end
  end

  defp cached_docs(path) do
    cache = Process.get(@cache_key) || %{}
    stat = File.stat(path)

    case Map.get(cache, path) do
      {^stat, docs} ->
        {:ok, docs}

      _ ->
        case extract_docs(path) do
          {:ok, docs} ->
            Process.put(@cache_key, Map.put(cache, path, {stat, docs}))
            {:ok, docs}

          {:error, _} = err ->
            err
        end
    end
  end

  defp extract_docs(path) do
    case File.read(path) do
      {:ok, src} ->
        result =
          with {:ok, tokens} <- Lexer.tokenize(src, file: path, emit_events: false),
               {:ok, ast} <- Parser.parse(tokens, file: path, emit_events: false) do
            {:ok, Extractor.extract(ast)}
          end

        case result do
          {:ok, docs} -> {:ok, docs}
          {:error, reason} -> {:error, {:source_diagnostic, reason, path, src}}
        end

      {:error, reason} ->
        {:error, {:source_diagnostic, {:file_read_error, path, reason}, path, nil}}
    end
  end

  defp render_extract_error(state, mod_name, {:source_diagnostic, reason, path, source}) do
    {diagnostic, registry} = Host.to_diagnostic(reason, path, source)

    Sink.new(
      format: :terminal,
      registry: registry,
      output_device: Map.get(state, :error_device, :stdio),
      color: if(Map.get(state, :color, false), do: :always, else: :never),
      width: 80
    )
    |> Sink.emit(diagnostic)
    |> Sink.flush()

    info(state, "(cannot extract docs for `#{mod_name}`)")
  end

  defp search_roots(state) do
    extras =
      state
      |> Map.get(:loaded, [])
      |> Enum.filter(&is_binary/1)
      |> Enum.map(&Path.dirname/1)

    configured =
      case Application.get_env(:cure, :repl) do
        kw when is_list(kw) -> Keyword.get(kw, :cure_source_roots, [])
        _ -> []
      end

    # `Paths.source_dirs/0` yields every stdlib candidate that exists:
    # an explicit override, the bundled `priv/std/` (populated by
    # `Mix.Tasks.Cure.BundleStdlib`), and the legacy cwd-relative
    # `lib/std/`. Prepending them to the search roots means host
    # applications -- notably the REPL embedded in `:cure_site` --
    # resolve `:doc Std.List` without any extra configuration.
    (Paths.source_dirs() ++ extras ++ configured)
    |> Enum.uniq()
    |> Enum.filter(&File.dir?/1)
  end

  defp find_in_root(root, module_name) do
    candidates = candidate_filenames(module_name)

    Enum.find_value(candidates, :not_found, fn rel ->
      path = Path.join(root, rel)

      cond do
        File.regular?(path) and module_matches?(path, module_name) -> {:ok, path}
        true -> nil
      end
    end)
  end

  # Build the likely on-disk filenames for a Cure module, from the most
  # conventional (`Std.List` -> `list.cure`) to the less conventional
  # (`My.Mod` -> `my.mod.cure`).
  defp candidate_filenames(module_name) do
    parts = String.split(module_name, ".")
    last = List.last(parts)

    [
      String.downcase(last) <> ".cure",
      last <> ".cure",
      (parts |> Enum.map(&String.downcase/1) |> Enum.join("_")) <> ".cure",
      String.replace(module_name, ".", "/") <> ".cure"
    ]
    |> Enum.uniq()
  end

  # Confirm the file's top-level `mod` declaration matches either the
  # requested name or its `Std.`-stripped variant.
  defp module_matches?(path, module_name) do
    with {:ok, src} <- File.read(path) do
      Regex.run(~r/^\s*mod\s+([A-Za-z_][\w\.]*)/m, src)
      |> case do
        [_, declared] ->
          declared == module_name or
            "Std." <> declared == module_name or
            "Cure." <> declared == module_name or
            declared == "Std." <> module_name

        _ ->
          false
      end
    else
      _ -> false
    end
  end

  # ==========================================================================
  # Helpers
  # ==========================================================================

  defp info(state, text) do
    styled = with_style(state, :info, text)
    Render.write_line(styled)
    :ok
  end

  defp with_style(%{theme: theme}, key, text) when is_atom(key) do
    style = Map.get(theme, key, "")
    if style == "", do: text, else: style <> text <> theme.reset
  end

  defp with_style(_state, _key, text), do: text

  defp strip_cure_prefix("Cure." <> rest), do: rest
  defp strip_cure_prefix(other), do: other

  defp lowercase_start?(""), do: false

  defp lowercase_start?(s) do
    first = String.first(s)
    first != nil and first == String.downcase(first) and first != String.upcase(first)
  end

  @doc """
  Return the stdlib module names in Cure source form (e.g. `"Std.List"`),
  suitable for pre-populating the REPL's `state.uses` on startup.

  Accepts the same `kind` argument as `Cure.Stdlib.Preload.stdlib_modules/1`
  and delegates to it. Defaults to `:none` so callers must opt into a
  non-empty selection (matching the "explicit over implicit" rule
  applied to the rest of the preload surface).
  """
  @spec default_uses(Preload.kind()) :: [String.t()]
  def default_uses(kind \\ :none) do
    Preload.stdlib_modules(kind)
    |> Enum.map(&Atom.to_string/1)
    |> Enum.map(&strip_cure_prefix/1)
  end
end
