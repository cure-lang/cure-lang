defmodule CureSiteWeb.LlmsController do
  @moduledoc """
  Serve an `llms.txt` document describing the site to large language
  models, in the format proposed by https://llmstxt.org/.

  The same payload is published at every casing variant the spec
  permits, both from the site root and under `/.well-known/`:

    * `/llms.txt`, `/llm.txt`, `/LLM.txt`, `/LLMS.txt`
    * `/.well-known/llms.txt`, `/.well-known/llm.txt`,
      `/.well-known/LLM.txt`, `/.well-known/LLMS.txt`

  The file is generated on the fly from the same content sources
  the rest of the site uses (`CureSite.Pages`, `CureSite.Blog`,
  `CureSite.Stdlib`) so a fresh redeploy is the only thing required
  to refresh it. Every link is absolute, derived from
  `CureSiteWeb.Endpoint.url/0`, so the file works regardless of the
  active host.
  """
  use CureSiteWeb, :controller

  alias CureSite.{Blog, Pages, Stdlib}
  alias CureSiteWeb.Endpoint

  @repo_url "https://github.com/cure-lang/cure-lang"
  @license_url "https://github.com/cure-lang/cure-lang/blob/main/LICENSE"

  @doc """
  Render the `llms.txt` document.

  All eight casing/path variants funnel through this single action.
  Each request is served from per-request state only; the rendering
  is fast enough that we keep it dynamic instead of caching.
  """
  def index(conn, _params) do
    body = render_document()

    conn
    |> put_resp_content_type("text/plain")
    |> send_resp(200, body)
  end

  # ---------------------------------------------------------------------------
  # Document assembly
  # ---------------------------------------------------------------------------

  defp render_document do
    base = base_url()
    version = safe_cure_version()

    [
      header(version),
      site_overview(base),
      documentation_section(base),
      stdlib_section(base),
      blog_section(base),
      tools_section(base),
      optional_section()
    ]
    |> Enum.reject(&(&1 in [nil, ""]))
    |> Enum.join("\n\n")
    |> Kernel.<>("\n")
  end

  # `# Title` line followed by the spec's `> blockquote` summary, then
  # a free-form paragraph that gives the model enough context to
  # decide which of the link sections below it actually wants to
  # crawl.
  defp header(version) do
    """
    # Cure v#{version}
    > Dependently typed programming for the BEAM through one kernel-checked compiler pipeline.

    Cure is an indentation-structured, expression-oriented language that compiles to BEAM bytecode and runs alongside Elixir and Erlang. Every program follows the same dependent pipeline: elaboration to dependent Core, independent kernel checking, quantitative erasure, and BEAM emission. Indexed families, total proofs, typed actors, finite-state machines, supervisors, and OTP applications are ordinary language constructs rather than separate compiler modes.

    This file is generated dynamically and reflects every page, blog post and standard-library module currently shipped with the site. A machine-readable XML companion is published at `/sitemap.xml`.\
    """
    |> String.trim_trailing()
  end

  # Hard-coded high-level pointers that don't fit cleanly under the
  # auto-discovered Documentation / Stdlib / Blog buckets but are
  # still useful entry points for an LLM.
  defp site_overview(base) do
    """
    ## Overview
    - [Home](#{base}/): Project landing page with the current release blurb and quick example.
    - [Sitemap](#{base}/sitemap.xml): Comprehensive XML sitemap of every indexable URL.
    - [Robots](#{base}/robots.txt): Crawler policy and sitemap discovery.\
    """
    |> String.trim_trailing()
  end

  # `Pages`, `Blog` and `Stdlib` all bake their content in at compile
  # time via NimblePublisher / `@external_resource`, so each list is
  # statically known to be non-empty in any deployable build. We
  # therefore skip the defensive empty-list branch -- the compiler's
  # type analysis flags it as unreachable -- and assume the bullet
  # list is always rendered.
  defp documentation_section(base) do
    items =
      Pages.all_pages()
      |> Enum.sort_by(&{negate(&1.order), &1.title})
      |> Enum.map_join("\n", fn page ->
        "- [#{page.title}](#{base}/#{page.id}): #{strip(page.description)}"
      end)

    "## Documentation\n" <> items
  end

  defp stdlib_section(base) do
    items =
      Stdlib.modules()
      |> Enum.map_join("\n", fn mod ->
        "- [#{mod.module}](#{base}/stdlib/#{mod.module}): #{describe_stdlib_module(mod)}"
      end)

    "## Standard Library\n" <>
      "Auto-generated API reference for every module under `lib/std/*.cure`. Every entry is also linked from `/stdlib`.\n\n" <>
      items
  end

  defp blog_section(base) do
    items =
      Blog.all_posts()
      |> Enum.map_join("\n", fn post ->
        "- [#{post.title}](#{base}/blog/#{post.id}) (#{Date.to_iso8601(post.date)}): #{strip(post.description)}"
      end)

    "## Blog\n" <> items
  end

  defp tools_section(base) do
    """
    ## Tools
    - [Playground](#{base}/playground): Two-pane editor with live syntax highlighting, bidirectional type-checking and a sandboxed evaluator.
    - [REPL](#{base}/repl): Browser-based access to the Cure interactive REPL.\
    """
    |> String.trim_trailing()
  end

  defp optional_section do
    """
    ## Optional
    - [Macro language](https://hexdocs.pm/cure/macros.html): Source-defined syntax, hygienic quotation, syntax families, and compile-time expansion.
    - [Proof authoring](https://hexdocs.pm/cure/proofs.html): Proof chains, rewriting, simplification, induction, and generated defining equations.
    - [Source repository](#{@repo_url}): The Cure compiler, standard library and CLI sources.
    - [License](#{@license_url}): Project licence.\
    """
    |> String.trim_trailing()
  end

  # ---------------------------------------------------------------------------
  # Helpers
  # ---------------------------------------------------------------------------

  defp base_url do
    Endpoint.url() |> String.trim_trailing("/")
  rescue
    _ -> ""
  end

  defp safe_cure_version do
    if function_exported?(Cure, :version, 0), do: Cure.version(), else: "unknown"
  end

  # Take the first paragraph of the moduledoc, normalise whitespace,
  # truncate it to a sentence-like fragment so the bullet stays on
  # one line in the rendered file.
  defp describe_stdlib_module(%{module_doc: doc}) when is_binary(doc) and doc != "" do
    doc
    |> String.split(~r/\n{2,}/, parts: 2)
    |> List.first("")
    |> normalise_whitespace()
    |> truncate(220)
    |> case do
      "" -> "API reference."
      text -> text
    end
  end

  defp describe_stdlib_module(_), do: "API reference."

  defp strip(nil), do: ""
  defp strip(text) when is_binary(text), do: normalise_whitespace(text)

  defp normalise_whitespace(text) do
    text
    |> String.replace(~r/\s+/u, " ")
    |> String.trim()
  end

  defp truncate(text, max) when byte_size(text) <= max, do: text

  defp truncate(text, max) do
    text
    |> String.slice(0, max - 1)
    |> Kernel.<>("…")
  end

  # Used only as a sort key. We want higher `order` first while
  # preserving lexicographic title ordering as a tie-breaker, so flip
  # the sign of the order before comparing.
  defp negate(n) when is_integer(n), do: -n
  defp negate(_), do: 0
end
