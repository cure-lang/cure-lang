defmodule CureSite.MarkdownConverter do
  @moduledoc """
  Markdown-to-HTML pipeline shared by the blog, pages, and stdlib
  renderer.

  The pipeline is:

      markdown
      |> interpolate_placeholders()
      |> MDEx.to_html!(mdex_options)
      |> highlight_code_blocks(highlighters)

  `MDEx` is a CommonMark + GFM parser backed by a Rust NIF. It lives
  in the site's runtime dependency closure (via `{:mdex, "~> 0.12"}`
  in `mix.exs`), unlike `Earmark`, which was only reachable
  transitively through `:nimble_publisher` and therefore disappeared
  from the release whenever that dependency was flagged
  `runtime: false`.

  Syntax highlighting is performed directly against `Makeup.Registry`
  instead of routing through `NimblePublisher.highlight/2`. Doing so
  keeps the runtime code path free of `NimblePublisher.*` calls, which
  matters for `CureSite.Stdlib.markdown_to_html/1`: stdlib module
  docs are rendered on demand in production, so the runtime pipeline
  must not require `:nimble_publisher` to be present in the release.

  Two entry points:

    * `convert/4` -- the `:html_converter` callback used by
      `CureSite.Blog` and `CureSite.Pages` at compile time.
    * `to_html/1,2` -- the runtime-safe helper used by
      `CureSite.Stdlib.markdown_to_html/1` (and anywhere else the
      site needs to render markdown outside of NimblePublisher).

  Before rendering, a small set of placeholders is substituted so
  markdown content can reference build-time values such as the
  current Cure version:

    * `{{cure_version}}`  -> the bare version string (e.g. `0.29.0`)
    * `{{cure_vversion}}` -> the version prefixed with `v`
      (e.g. `v0.29.0`)
  """

  @default_highlighters [:makeup_cure, :makeup_elixir, :makeup_erlang]

  @doc """
  `NimblePublisher` `:html_converter` callback.

  Handles `.md` / `.markdown` files; returns `nil` for every other
  extension so NimblePublisher falls back to the raw body.
  """
  def convert(filepath, body, _attrs, opts) do
    if Path.extname(filepath) in [".md", ".markdown"] do
      highlighters = Keyword.get(opts, :highlighters, [])
      to_html(body, highlighters)
    end
  end

  @doc """
  Render `markdown` to HTML.

  Interpolates build-time placeholders, runs the result through
  `MDEx.to_html!/2` with GFM extensions enabled, and syntax-
  highlights any fenced code block whose language is registered with
  `Makeup`. `nil` and `""` inputs yield `""` so callers can blindly
  splice the result into a template.
  """
  @spec to_html(String.t() | nil, [atom()]) :: String.t()
  def to_html(markdown, highlighters \\ @default_highlighters)
  def to_html(nil, _highlighters), do: ""
  def to_html("", _highlighters), do: ""

  def to_html(markdown, highlighters) when is_binary(markdown) do
    markdown
    |> interpolate_placeholders()
    |> MDEx.to_html!(mdex_options())
    |> highlight_code_blocks(highlighters)
  end

  @doc """
  Substitute the supported placeholders in `body` with their
  compile-time values.
  """
  @spec interpolate_placeholders(String.t()) :: String.t()
  def interpolate_placeholders(body) when is_binary(body) do
    version = CureSite.cure_version()

    body
    |> String.replace("{{cure_version}}", version)
    |> String.replace("{{cure_vversion}}", "v" <> version)
  end

  # -- MDEx wiring -----------------------------------------------------------

  # Options chosen to stay close to Earmark's previous behaviour:
  #
  #   * `render: [unsafe: true]` -> raw HTML in markdown passes through
  #     (Earmark does this by default; MDEx escapes it unless told
  #     otherwise).
  #   * GFM extensions (tables, strikethrough, autolinks, task lists,
  #     footnotes) are enabled because the existing posts and pages
  #     rely on them.
  #   * `syntax_highlight: nil` disables MDEx's built-in syntax
  #     highlighter so the Makeup-based pass below keeps ownership of
  #     the visual styling (the site already ships Makeup's stylesheet
  #     and CSS classes).
  defp mdex_options do
    [
      render: [unsafe: true],
      extension: [
        table: true,
        strikethrough: true,
        autolink: true,
        tasklist: true,
        footnotes: true
      ],
      syntax_highlight: nil
    ]
  end

  # -- Syntax highlighting ---------------------------------------------------

  # Mirrors `NimblePublisher.Highlighter` but depends only on
  # `:makeup`, which is already a direct runtime dependency of the
  # site. Lexers that are not registered at runtime (for example
  # `:makeup_elixir` when it is compiled with `runtime: false`) fall
  # through to a plain `<pre><code class="lang">` block, matching the
  # previous behaviour of `NimblePublisher.highlight/2`.
  defp highlight_code_blocks(html, []), do: html

  defp highlight_code_blocks(html, _highlighters) do
    # MDEx (comrak) emits fenced code blocks as
    #   `<pre><code class="language-foo">escaped-body</code></pre>`,
    # while Earmark and plain CommonMark renderers drop the `language-`
    # prefix. The regex accepts both forms so we can stay agnostic if
    # the renderer ever changes.
    code_block_regex =
      ~r|<pre><code\s+class="(?:language-)?(?<lang>[^"\s]+)">(?<body>[^<]*)</code></pre>|

    Regex.replace(code_block_regex, html, fn _full, lang, escaped_body ->
      case Makeup.Registry.fetch_lexer_by_name(lang) do
        {:ok, {lexer, lexer_opts}} ->
          highlighted =
            escaped_body
            |> unescape_html()
            |> IO.iodata_to_binary()
            |> Makeup.highlight_inner_html(
              lexer: lexer,
              lexer_options: lexer_opts,
              formatter_options: [highlight_tag: "span"]
            )

          wrap_code_block(lang, ~s(<code class="makeup #{lang}">#{highlighted}</code>))

        :error ->
          wrap_code_block(lang, ~s(<code class="#{lang}">#{escaped_body}</code>))
      end
    end)
  end

  defp wrap_code_block(lang, code) do
    ~s(<div class="cure-code-window"><div class="cure-code-window-bar"><span class="cure-code-window-dots" aria-hidden="true"><i></i><i></i><i></i></span><span class="cure-code-window-label">#{lang}</span></div><pre>#{code}</pre></div>)
  end

  @entities [
    {"&amp;", ?&},
    {"&lt;", ?<},
    {"&gt;", ?>},
    {"&quot;", ?\"},
    {"&#39;", ?'},
    {"&lbrace;", ?{},
    {"&rbrace;", ?}}
  ]

  for {encoded, decoded} <- @entities do
    defp unescape_html(unquote(encoded) <> rest),
      do: [unquote(decoded) | unescape_html(rest)]
  end

  defp unescape_html(<<c, rest::binary>>), do: [c | unescape_html(rest)]
  defp unescape_html(<<>>), do: []
end
