defmodule Cure.Doc.HTMLGenerator do
  @moduledoc """
  Static HTML documentation generator for `cure doc`.

  The output layout mirrors ExDoc's two-pane experience:

    * A persistent left sidebar lists orphan pages (`extras` from the
      `[doc]` section of `Cure.toml`) and every extracted module,
      optionally grouped via `[doc.groups_for_modules]`.
    * The right pane shows the page or module the user clicked. Every
      function, type, and interface inside a module page gets an
      anchor (`#fn-<name>`, `#type-<name>`, `#interface-<name>`) so deep
      links work out of the box.
    * A small vanilla-JS bundle implements a sidebar filter (press `/`
      to focus) and a `prefers-color-scheme`-driven theme toggle.

  `##` doc comments are routed through `Cure.Doc.Markdown`, which in
  turn wraps `Md.generate/1`, so fenced code blocks, lists, bold /
  italics, links, and tables all render natively.
  """

  alias Cure.Doc.Markdown

  @default_title "Cure Documentation"

  @doc """
  Render HTML documentation for a list of extracted module doc maps.

  Writes per-module pages, per-extra pages, a shared `style.css`, and
  an `assets.js` bundle to `output_dir`. Returns `:ok` on success.

  Supported options:

    * `:title`        -- title shown in the sidebar header.
    * `:doc_config`   -- the map returned by
      `Cure.Project.normalize_doc/2`. Missing keys fall through to
      sensible defaults.
    * `:project_root` -- base directory used to resolve relative
      paths in `:extras`.
    * `:cure_version` -- version string shown in the footer.
  """
  @spec generate([map()], String.t(), keyword()) :: :ok
  def generate(modules, output_dir, opts \\ []) do
    File.mkdir_p!(output_dir)

    title = Keyword.get(opts, :title, @default_title)
    doc_config = normalize_doc_config(Keyword.get(opts, :doc_config, %{}))
    project_root = Keyword.get(opts, :project_root, File.cwd!())
    cure_version = Keyword.get(opts, :cure_version, safe_version())

    extras = collect_extras(doc_config.extras, project_root)
    groups = group_modules(modules, doc_config.groups_for_modules)

    File.write!(Path.join(output_dir, "style.css"), css())
    File.write!(Path.join(output_dir, "assets.js"), js())

    sidebar = render_sidebar(title, doc_config, extras, groups)

    Enum.each(extras, fn extra ->
      File.write!(
        Path.join(output_dir, extra.slug <> ".html"),
        wrap_page(
          extra.title <> " - " <> title,
          sidebar,
          render_extra(extra),
          extra.slug,
          cure_version
        )
      )
    end)

    Enum.each(modules, fn mod ->
      slug = module_slug(mod.module)

      File.write!(
        Path.join(output_dir, slug <> ".html"),
        wrap_page(
          "#{mod.module} - #{title}",
          sidebar,
          render_module(mod),
          slug,
          cure_version
        )
      )
    end)

    main_slug = resolve_main_slug(doc_config.main)

    index_html =
      case find_main(main_slug, extras, modules) do
        {:extra, extra} ->
          wrap_page(title, sidebar, render_extra(extra), extra.slug, cure_version)

        {:module, mod} ->
          wrap_page(
            "#{mod.module} - #{title}",
            sidebar,
            render_module(mod),
            module_slug(mod.module),
            cure_version
          )

        :none ->
          wrap_page(
            title,
            sidebar,
            render_module_index(title, modules),
            "index",
            cure_version
          )
      end

    File.write!(Path.join(output_dir, "index.html"), index_html)

    :ok
  end

  # -- Config normalization ---------------------------------------------------

  defp normalize_doc_config(nil), do: normalize_doc_config(%{})

  defp normalize_doc_config(map) when is_map(map) do
    %{
      main: Map.get(map, :main),
      title: Map.get(map, :title),
      extras: Map.get(map, :extras, []) |> List.wrap(),
      logo: Map.get(map, :logo),
      source_url: Map.get(map, :source_url),
      source_ref: Map.get(map, :source_ref),
      groups_for_modules: Map.get(map, :groups_for_modules, [])
    }
  end

  defp safe_version do
    try do
      Cure.version()
    rescue
      _ -> ""
    end
  end

  # -- Extras -----------------------------------------------------------------

  defp collect_extras(paths, project_root) when is_list(paths) do
    paths
    |> Enum.map(&Path.expand(&1, project_root))
    |> Enum.filter(&File.regular?/1)
    |> Enum.map(fn path ->
      body = File.read!(path)
      basename = Path.rootname(Path.basename(path))

      %{
        source: path,
        slug: slugify(basename),
        title: derive_title(body, basename),
        body: body
      }
    end)
  end

  defp collect_extras(_, _), do: []

  defp derive_title(body, fallback) do
    case Regex.run(~r/^\s*#\s+(.+)$/m, body) do
      [_, title] -> String.trim(title)
      _ -> fallback
    end
  end

  defp slugify(name) do
    name
    |> String.downcase()
    |> String.replace(~r/[^a-z0-9]+/, "_")
    |> String.trim("_")
  end

  # -- Module grouping --------------------------------------------------------

  defp group_modules(modules, group_spec) do
    sorted = Enum.sort_by(modules, & &1.module)

    case group_spec do
      [] ->
        [{"Modules", sorted}]

      _ ->
        assigned =
          Enum.flat_map(group_spec, fn {group_name, members} ->
            matched = Enum.filter(sorted, &(&1.module in members))
            if matched == [], do: [], else: [{group_name, matched}]
          end)

        declared = Enum.flat_map(group_spec, fn {_, m} -> m end)
        leftover = Enum.reject(sorted, &(&1.module in declared))

        if leftover == [], do: assigned, else: assigned ++ [{"Other", leftover}]
    end
  end

  # -- Sidebar ----------------------------------------------------------------

  defp render_sidebar(title, doc_config, extras, groups) do
    logo_html =
      case doc_config.logo do
        nil -> ""
        path -> ~s(<img src="#{esc(path)}" alt="Logo" class="cure-doc-logo">)
      end

    extras_html =
      if extras == [] do
        ""
      else
        items =
          Enum.map_join(extras, "\n", fn ex ->
            ~s(<li><a href="#{esc(ex.slug)}.html" data-slug="#{esc(ex.slug)}">#{esc(ex.title)}</a></li>)
          end)

        """
        <section class="cure-doc-section">
          <h2>Pages</h2>
          <ul class="cure-doc-list">
        #{items}
          </ul>
        </section>
        """
      end

    groups_html =
      Enum.map_join(groups, "\n", fn {group_name, mods} ->
        items =
          Enum.map_join(mods, "\n", fn m ->
            slug = module_slug(m.module)

            ~s(<li><a href="#{esc(slug)}.html" data-slug="#{esc(slug)}">#{esc(m.module)}</a></li>)
          end)

        """
        <section class="cure-doc-section">
          <h2>#{esc(group_name)}</h2>
          <ul class="cure-doc-list">
        #{items}
          </ul>
        </section>
        """
      end)

    """
    <aside class="cure-doc-sidebar">
      <header class="cure-doc-sidebar-head">
        #{logo_html}
        <h1><a href="index.html">#{esc(title)}</a></h1>
      </header>
      <input
        type="search"
        id="cure-doc-filter"
        class="cure-doc-filter"
        placeholder="Filter (press /)"
        autocomplete="off"
        aria-label="Filter sidebar">
      <nav class="cure-doc-nav">
    #{extras_html}
    #{groups_html}
      </nav>
    </aside>
    """
  end

  defp resolve_main_slug(nil), do: nil
  defp resolve_main_slug(main) when is_binary(main), do: slugify(Path.rootname(Path.basename(main)))
  defp resolve_main_slug(_), do: nil

  defp find_main(nil, _extras, _modules), do: :none

  defp find_main(slug, extras, modules) do
    case Enum.find(extras, &(&1.slug == slug)) do
      nil ->
        case Enum.find(modules, fn m -> module_slug(m.module) == slug end) do
          nil -> :none
          mod -> {:module, mod}
        end

      extra ->
        {:extra, extra}
    end
  end

  # -- Extra page rendering ---------------------------------------------------

  defp render_extra(extra) do
    """
    <article class="cure-doc-article cure-doc-extra">
    #{Markdown.to_html(extra.body)}
    </article>
    """
  end

  # -- Module index -----------------------------------------------------------

  defp render_module_index(title, modules) do
    items =
      modules
      |> Enum.sort_by(& &1.module)
      |> Enum.map_join("\n", fn mod ->
        slug = module_slug(mod.module)

        fn_count = length(mod.functions || [])

        preview =
          (mod.module_doc || "")
          |> first_paragraph()
          |> Markdown.to_html()

        """
        <li>
          <a href="#{esc(slug)}.html"><strong>#{esc(mod.module)}</strong></a>
          <span class="cure-doc-muted">#{fn_count} function#{if fn_count == 1, do: "", else: "s"}</span>
          <div class="cure-doc-preview">#{preview}</div>
        </li>
        """
      end)

    """
    <article class="cure-doc-article">
      <h1>#{esc(title)}</h1>
      <p class="cure-doc-muted">#{length(modules)} module#{if length(modules) == 1, do: "", else: "s"}</p>
      <ul class="cure-doc-module-index">
    #{items}
      </ul>
    </article>
    """
  end

  defp first_paragraph(text) do
    text
    |> String.split(~r/\n\s*\n/, parts: 2)
    |> List.first()
    |> to_string()
  end

  # -- Module page ------------------------------------------------------------

  defp render_module(mod) do
    module_doc_html =
      case mod.module_doc do
        nil -> ""
        "" -> ""
        md -> ~s(<section class="cure-doc-summary">#{Markdown.to_html(md)}</section>)
      end

    types_html = render_types(mod.types || [])
    protocols_html = render_protocols(mod.protocols || [])
    functions_html = render_functions(mod.functions || [])
    toc_html = render_toc(mod)

    """
    <article class="cure-doc-article">
      <header class="cure-doc-article-head">
        <h1>#{esc(mod.module)}</h1>
      </header>
      #{toc_html}
      #{module_doc_html}
      #{types_html}
      #{protocols_html}
      #{functions_html}
    </article>
    """
  end

  defp render_toc(mod) do
    public_fns =
      (mod.functions || [])
      |> Enum.filter(&(&1.visibility == :public))
      |> Enum.sort_by(& &1.name)

    fn_links =
      Enum.map_join(public_fns, "\n", fn f ->
        ~s(<li><a href="#fn-#{esc(f.name)}"><code>#{esc(f.name)}/#{length(f.params)}</code></a></li>)
      end)

    type_links =
      Enum.map_join(mod.types || [], "\n", fn t ->
        ~s(<li><a href="#type-#{esc(t.name)}"><code>#{esc(t.name)}</code></a></li>)
      end)

    interface_links =
      Enum.map_join(mod.protocols || [], "\n", fn p ->
        ~s(<li><a href="#interface-#{esc(p.name)}"><code>#{esc(p.name)}</code></a></li>)
      end)

    sections =
      [
        if(type_links != "", do: {"Types", type_links}, else: nil),
        if(interface_links != "", do: {"Interfaces", interface_links}, else: nil),
        if(fn_links != "", do: {"Functions", fn_links}, else: nil)
      ]
      |> Enum.reject(&is_nil/1)

    if sections == [] do
      ""
    else
      blocks =
        Enum.map_join(sections, "\n", fn {label, items} ->
          ~s(<section><h3>#{esc(label)}</h3><ul>#{items}</ul></section>)
        end)

      ~s(<nav class="cure-doc-toc" aria-label="On this page">#{blocks}</nav>)
    end
  end

  defp render_functions([]), do: ""

  defp render_functions(functions) do
    public_fns = Enum.filter(functions, &(&1.visibility == :public))

    body =
      if public_fns == [] do
        ~s(<p class="cure-doc-muted">No public functions.</p>)
      else
        public_fns
        |> Enum.sort_by(&{&1.name, length(&1.params)})
        |> Enum.map_join("\n", &render_function/1)
      end

    """
    <section class="cure-doc-functions">
      <h2>Functions</h2>
      #{body}
    </section>
    """
  end

  defp render_function(f) do
    params_str =
      Enum.map_join(f.params, ", ", fn {name, type} ->
        ~s(#{esc(name)}: <span class="cure-doc-type">#{esc(type)}</span>)
      end)

    ret_str =
      if f.return_type,
        do: ~s( -&gt; <span class="cure-doc-type">#{esc(f.return_type)}</span>),
        else: ""

    effects_str =
      if f.effects != [] do
        effs = Enum.join(f.effects, ", ")
        ~s( <span class="cure-doc-effect">! #{esc(effs)}</span>)
      else
        ""
      end

    badges =
      [
        if(f.extern, do: ~s(<span class="cure-doc-badge extern">extern</span>), else: nil),
        if(f.guards, do: ~s(<span class="cure-doc-badge guard">guarded</span>), else: nil),
        if(f.clauses > 1,
          do: ~s(<span class="cure-doc-badge clauses">#{f.clauses} clauses</span>),
          else: nil
        )
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join(" ")

    doc_html =
      case f.doc do
        nil -> ""
        "" -> ""
        body -> ~s(<div class="cure-doc-function-doc">#{Markdown.to_html(body)}</div>)
      end

    """
    <article class="cure-doc-function" id="fn-#{esc(f.name)}">
      <h3 class="cure-doc-function-signature">
        <a href="#fn-#{esc(f.name)}" class="cure-doc-anchor" aria-label="Link to this function">#</a>
        <span class="cure-doc-keyword">fn</span>
        <span class="cure-doc-name">#{esc(f.name)}</span>(#{params_str})#{ret_str}#{effects_str}
        #{badges}
      </h3>
      #{doc_html}
    </article>
    """
  end

  defp render_types([]), do: ""

  defp render_types(types) do
    items =
      Enum.map_join(types, "\n", fn t ->
        doc_html =
          case t.doc do
            nil -> ""
            "" -> ""
            body -> ~s(<div class="cure-doc-type-doc">#{Markdown.to_html(body)}</div>)
          end

        variants =
          cond do
            Map.has_key?(t, :variants) and is_list(t.variants) and t.variants != [] ->
              " = " <> Enum.join(t.variants, " | ")

            true ->
              ""
          end

        """
        <article class="cure-doc-type-entry" id="type-#{esc(t.name)}">
          <h3>
            <a href="#type-#{esc(t.name)}" class="cure-doc-anchor" aria-label="Link to this type">#</a>
            <code>type #{esc(t.name)}#{esc(variants)}</code>
          </h3>
          #{doc_html}
        </article>
        """
      end)

    """
    <section class="cure-doc-types">
      <h2>Types</h2>
      #{items}
    </section>
    """
  end

  defp render_protocols([]), do: ""

  defp render_protocols(protocols) do
    items =
      Enum.map_join(protocols, "\n", fn p ->
        tp = if p.type_params != [], do: "(#{Enum.join(p.type_params, ", ")})", else: ""

        methods =
          Enum.map_join(p.methods || [], ", ", fn m ->
            name = Map.get(m, :name, "?")
            ~s(<code>#{esc(name)}</code>)
          end)

        doc_html =
          case p.doc do
            nil -> ""
            "" -> ""
            body -> ~s(<div class="cure-doc-proto-doc">#{Markdown.to_html(body)}</div>)
          end

        """
        <article class="cure-doc-proto-entry" id="interface-#{esc(p.name)}">
          <h3>
            <a href="#interface-#{esc(p.name)}" class="cure-doc-anchor" aria-label="Link to this interface">#</a>
            <code>interface #{esc(p.name)}#{esc(tp)}</code>
          </h3>
          <p class="cure-doc-muted">Methods: #{methods}</p>
          #{doc_html}
        </article>
        """
      end)

    """
    <section class="cure-doc-protocols">
      <h2>Interfaces</h2>
      #{items}
    </section>
    """
  end

  # -- HTML shell -------------------------------------------------------------

  defp wrap_page(title, sidebar, body, active_slug, cure_version) do
    """
    <!DOCTYPE html>
    <html lang="en">
    <head>
      <meta charset="utf-8">
      <meta name="viewport" content="width=device-width, initial-scale=1">
      <title>#{esc(title)}</title>
      <link rel="stylesheet" href="style.css">
    </head>
    <body data-active="#{esc(active_slug)}">
      <div class="cure-doc-shell">
    #{sidebar}
        <main class="cure-doc-main">
          <header class="cure-doc-topbar">
            <button id="cure-doc-theme" type="button" class="cure-doc-theme-toggle" aria-label="Toggle theme">
              <span class="cure-doc-theme-sun">&#9728;</span>
              <span class="cure-doc-theme-moon">&#9790;</span>
            </button>
          </header>
    #{body}
          <footer class="cure-doc-footer">
            Generated by <code>cure doc</code>#{version_suffix(cure_version)}.
          </footer>
        </main>
      </div>
      <script src="assets.js"></script>
    </body>
    </html>
    """
  end

  defp version_suffix(""), do: ""
  defp version_suffix(nil), do: ""
  defp version_suffix(version), do: " (Cure v#{esc(version)})"

  defp module_slug(name) do
    name
    |> to_string()
    |> String.replace(".", "_")
    |> String.downcase()
  end

  defp esc(nil), do: ""

  defp esc(s) when is_binary(s) do
    s
    |> String.replace("&", "&amp;")
    |> String.replace("<", "&lt;")
    |> String.replace(">", "&gt;")
    |> String.replace("\"", "&quot;")
  end

  defp esc(other), do: esc(to_string(other))

  # -- CSS / JS ---------------------------------------------------------------

  defp css do
    """
    :root {
      --cure-bg: #ffffff;
      --cure-fg: #1f2937;
      --cure-muted: #6b7280;
      --cure-accent: #2563eb;
      --cure-accent-strong: #1d4ed8;
      --cure-border: #e5e7eb;
      --cure-sidebar-bg: #f9fafb;
      --cure-sidebar-fg: #1f2937;
      --cure-code-bg: #f3f4f6;
      --cure-badge-extern: #fef3c7;
      --cure-badge-extern-fg: #92400e;
      --cure-badge-guard: #dbeafe;
      --cure-badge-guard-fg: #1e40af;
      --cure-badge-clauses: #f3e8ff;
      --cure-badge-clauses-fg: #6b21a8;
      --cure-effect: #dc2626;
    }

    @media (prefers-color-scheme: dark) {
      :root:not([data-cure-theme="light"]) {
        --cure-bg: #0b1120;
        --cure-fg: #e2e8f0;
        --cure-muted: #94a3b8;
        --cure-accent: #60a5fa;
        --cure-accent-strong: #93c5fd;
        --cure-border: #1e293b;
        --cure-sidebar-bg: #111827;
        --cure-sidebar-fg: #e2e8f0;
        --cure-code-bg: #1e293b;
        --cure-badge-extern: #78350f;
        --cure-badge-extern-fg: #fef3c7;
        --cure-badge-guard: #1e3a8a;
        --cure-badge-guard-fg: #dbeafe;
        --cure-badge-clauses: #581c87;
        --cure-badge-clauses-fg: #f3e8ff;
        --cure-effect: #f87171;
      }
    }

    :root[data-cure-theme="dark"] {
      --cure-bg: #0b1120;
      --cure-fg: #e2e8f0;
      --cure-muted: #94a3b8;
      --cure-accent: #60a5fa;
      --cure-accent-strong: #93c5fd;
      --cure-border: #1e293b;
      --cure-sidebar-bg: #111827;
      --cure-sidebar-fg: #e2e8f0;
      --cure-code-bg: #1e293b;
      --cure-badge-extern: #78350f;
      --cure-badge-extern-fg: #fef3c7;
      --cure-badge-guard: #1e3a8a;
      --cure-badge-guard-fg: #dbeafe;
      --cure-badge-clauses: #581c87;
      --cure-badge-clauses-fg: #f3e8ff;
      --cure-effect: #f87171;
    }

    * { box-sizing: border-box; }
    html, body { margin: 0; padding: 0; }

    body {
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
      background: var(--cure-bg);
      color: var(--cure-fg);
      line-height: 1.6;
    }

    a { color: var(--cure-accent); text-decoration: none; }
    a:hover { text-decoration: underline; color: var(--cure-accent-strong); }

    code, pre, .cure-doc-type, .cure-doc-name, .cure-doc-keyword {
      font-family: "JetBrains Mono", ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      font-size: 0.9em;
    }

    .cure-doc-shell {
      display: grid;
      grid-template-columns: 280px minmax(0, 1fr);
      min-height: 100vh;
    }

    .cure-doc-sidebar {
      background: var(--cure-sidebar-bg);
      color: var(--cure-sidebar-fg);
      border-right: 1px solid var(--cure-border);
      padding: 1.25rem 1rem 2rem;
      position: sticky;
      top: 0;
      align-self: start;
      height: 100vh;
      overflow-y: auto;
    }

    .cure-doc-sidebar-head { display: flex; align-items: center; gap: 0.6rem; margin-bottom: 1rem; }
    .cure-doc-sidebar-head h1 { font-size: 1.1rem; margin: 0; }
    .cure-doc-sidebar-head a { color: inherit; }
    .cure-doc-logo { width: 28px; height: 28px; }

    .cure-doc-filter {
      width: 100%;
      border: 1px solid var(--cure-border);
      background: var(--cure-bg);
      color: var(--cure-fg);
      padding: 0.45rem 0.6rem;
      border-radius: 6px;
      margin-bottom: 1rem;
      font-size: 0.85rem;
    }

    .cure-doc-section { margin-top: 1.25rem; }
    .cure-doc-section h2 {
      font-size: 0.72rem;
      text-transform: uppercase;
      letter-spacing: 0.08em;
      color: var(--cure-muted);
      margin: 0 0 0.4rem;
    }

    .cure-doc-list { list-style: none; padding: 0; margin: 0; }
    .cure-doc-list li { margin: 0.1rem 0; }
    .cure-doc-list a {
      display: block;
      padding: 0.25rem 0.5rem;
      border-radius: 4px;
      color: inherit;
    }
    .cure-doc-list a:hover { background: var(--cure-border); text-decoration: none; }
    .cure-doc-list a.cure-doc-active {
      background: var(--cure-accent);
      color: #fff;
    }

    .cure-doc-main {
      padding: 1.25rem 2.5rem 4rem;
      min-width: 0;
      max-width: 980px;
    }

    .cure-doc-topbar {
      display: flex;
      justify-content: flex-end;
      margin-bottom: 0.5rem;
    }

    .cure-doc-theme-toggle {
      background: transparent;
      border: 1px solid var(--cure-border);
      border-radius: 999px;
      padding: 0.35rem 0.6rem;
      cursor: pointer;
      color: var(--cure-fg);
    }
    .cure-doc-theme-toggle .cure-doc-theme-moon { display: none; }
    :root[data-cure-theme="dark"] .cure-doc-theme-toggle .cure-doc-theme-sun { display: none; }
    :root[data-cure-theme="dark"] .cure-doc-theme-toggle .cure-doc-theme-moon { display: inline; }

    .cure-doc-article { padding: 0 0 4rem; }
    .cure-doc-article h1 { margin: 0 0 1rem; font-size: 2rem; }
    .cure-doc-article h2 {
      margin: 2.5rem 0 1rem;
      padding-bottom: 0.4rem;
      border-bottom: 1px solid var(--cure-border);
    }
    .cure-doc-article h3 { margin: 1.2rem 0 0.5rem; }

    .cure-doc-article-head { margin-bottom: 1.25rem; }

    .cure-doc-muted { color: var(--cure-muted); font-size: 0.9em; }

    .cure-doc-toc {
      border: 1px solid var(--cure-border);
      border-radius: 8px;
      padding: 0.75rem 1rem;
      margin-bottom: 1.5rem;
      background: var(--cure-sidebar-bg);
    }
    .cure-doc-toc h3 {
      font-size: 0.75rem;
      text-transform: uppercase;
      margin: 0.3rem 0;
      color: var(--cure-muted);
    }
    .cure-doc-toc ul { list-style: none; padding: 0; margin: 0 0 0.5rem; display: flex; flex-wrap: wrap; gap: 0.4rem 0.8rem; }

    .cure-doc-summary { margin-bottom: 1.5rem; }

    .cure-doc-function,
    .cure-doc-type-entry,
    .cure-doc-proto-entry {
      border: 1px solid var(--cure-border);
      border-radius: 8px;
      padding: 1rem 1.25rem;
      margin-bottom: 1rem;
      background: var(--cure-sidebar-bg);
    }

    .cure-doc-function-signature { font-weight: 500; }
    .cure-doc-anchor {
      opacity: 0;
      margin-right: 0.25rem;
      font-weight: 300;
      text-decoration: none;
    }
    .cure-doc-function:hover .cure-doc-anchor,
    .cure-doc-type-entry:hover .cure-doc-anchor,
    .cure-doc-proto-entry:hover .cure-doc-anchor {
      opacity: 0.6;
    }

    .cure-doc-keyword { color: #9333ea; font-weight: 600; }
    .cure-doc-name { color: var(--cure-accent-strong); }
    .cure-doc-type { color: #059669; }
    .cure-doc-effect { color: var(--cure-effect); font-weight: 500; }

    .cure-doc-badge {
      font-size: 0.7rem;
      padding: 0.15rem 0.45rem;
      border-radius: 999px;
      margin-left: 0.25rem;
      vertical-align: middle;
    }
    .cure-doc-badge.extern { background: var(--cure-badge-extern); color: var(--cure-badge-extern-fg); }
    .cure-doc-badge.guard  { background: var(--cure-badge-guard);  color: var(--cure-badge-guard-fg); }
    .cure-doc-badge.clauses { background: var(--cure-badge-clauses); color: var(--cure-badge-clauses-fg); }

    .cure-doc-function-doc p:first-child,
    .cure-doc-type-doc p:first-child,
    .cure-doc-proto-doc p:first-child { margin-top: 0.5rem; }

    pre.cure-doc-code,
    .cure-doc-extra pre,
    .cure-doc-function-doc pre,
    .cure-doc-summary pre {
      background: var(--cure-code-bg);
      border: 1px solid var(--cure-border);
      border-radius: 6px;
      padding: 0.75rem 1rem;
      overflow-x: auto;
      font-size: 0.85rem;
      line-height: 1.45;
    }

    code.code-inline,
    .cure-doc-article code:not(pre code) {
      background: var(--cure-code-bg);
      padding: 0.12rem 0.35rem;
      border-radius: 4px;
      font-size: 0.85em;
    }

    .cure-doc-module-index { list-style: none; padding: 0; }
    .cure-doc-module-index li {
      border-bottom: 1px solid var(--cure-border);
      padding: 0.75rem 0;
    }
    .cure-doc-module-index strong { font-size: 1.05rem; }
    .cure-doc-preview p { margin: 0.25rem 0 0; color: var(--cure-muted); font-size: 0.9em; }

    .cure-doc-footer {
      margin-top: 4rem;
      padding-top: 1rem;
      border-top: 1px solid var(--cure-border);
      color: var(--cure-muted);
      font-size: 0.8rem;
    }

    @media (max-width: 900px) {
      .cure-doc-shell { grid-template-columns: 1fr; }
      .cure-doc-sidebar { position: static; height: auto; }
      .cure-doc-main { padding: 1rem; }
    }
    """ <> makeup_css()
  end

  # Emits the default Makeup stylesheet so syntax-highlighted code has
  # colour the moment the generated pages are opened. Best-effort: if
  # the stylesheet helper is unavailable, we fall through silently.
  defp makeup_css do
    try do
      "\n" <> Makeup.stylesheet(Makeup.Styles.HTML.StyleMap.tango_style())
    rescue
      _ -> ""
    catch
      _, _ -> ""
    end
  end

  defp js do
    """
    (function () {
      var filter = document.getElementById('cure-doc-filter');
      var active = document.body ? document.body.getAttribute('data-active') : null;

      if (active) {
        var links = document.querySelectorAll('.cure-doc-list a[data-slug]');
        for (var i = 0; i < links.length; i++) {
          if (links[i].getAttribute('data-slug') === active) {
            links[i].classList.add('cure-doc-active');
          }
        }
      }

      if (filter) {
        filter.addEventListener('input', function () {
          var needle = filter.value.toLowerCase();
          var items = document.querySelectorAll('.cure-doc-list li');
          for (var j = 0; j < items.length; j++) {
            var text = items[j].textContent.toLowerCase();
            items[j].style.display = needle === '' || text.indexOf(needle) !== -1 ? '' : 'none';
          }
        });

        document.addEventListener('keydown', function (ev) {
          if (ev.key === '/' && document.activeElement !== filter) {
            ev.preventDefault();
            filter.focus();
          }
        });
      }

      var toggle = document.getElementById('cure-doc-theme');
      var root = document.documentElement;

      function applyTheme(t) {
        if (t === 'dark' || t === 'light') {
          root.setAttribute('data-cure-theme', t);
        } else {
          root.removeAttribute('data-cure-theme');
        }
      }

      try {
        var stored = localStorage.getItem('cure-doc-theme');
        if (stored) applyTheme(stored);
      } catch (_) {}

      if (toggle) {
        toggle.addEventListener('click', function () {
          var next = root.getAttribute('data-cure-theme') === 'dark' ? 'light' : 'dark';
          applyTheme(next);
          try { localStorage.setItem('cure-doc-theme', next); } catch (_) {}
        });
      }
    }());
    """
  end
end
