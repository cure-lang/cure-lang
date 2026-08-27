defmodule CureSite.Pages.TechnicalOverview do
  @moduledoc """
  The `/about` page, rendered from the language repository's canonical
  technical overview (`docs/TECHNICAL_OVERVIEW.md`).

  Unlike every other entry of `CureSite.Pages`, this page has no
  markdown file under `priv/pages`. The document is maintained in the
  repository next to the compiler it describes, and the site reads it
  at compile time, so the "About" menu entry can never drift from the
  repository copy.

  Two adjustments are applied to the raw document:

    * the leading `# ...` heading is dropped, because
      `page_html/show.html.heex` already renders the page title as the
      `<h1>` and keeping both would duplicate it;
    * the body goes through `CureSite.MarkdownConverter` -- the same
      MDEx + Makeup pipeline the `priv/pages` entries use -- so code
      blocks are highlighted exactly like the rest of the docs.

  The document is registered as an `@external_resource`, so editing it
  recompiles this module and, transitively, `CureSite.Pages`.
  """

  alias CureSite.MarkdownConverter
  alias CureSite.Pages.Page

  # Mirrors the `:highlighters` list `CureSite.Pages` hands to
  # NimblePublisher, so both rendering paths agree.
  @highlighters [:makeup_cure, :makeup_elixir, :makeup_erlang]

  # `__DIR__` is `<repo>/site/lib/cure_site/pages` and the document
  # lives in `<repo>/docs`. `CureSite.cure_version/0` reaches the
  # top-level `mix.exs` the same way.
  @source_path Path.expand("../../../../docs/TECHNICAL_OVERVIEW.md", __DIR__)
  @external_resource @source_path

  unless File.exists?(@source_path) do
    raise """
    #{@source_path} is missing.

    The site's /about page is rendered from the language repository's
    technical overview. Restore the document, or update
    CureSite.Pages.TechnicalOverview, before compiling the site.
    """
  end

  @source File.read!(@source_path)

  @markdown (case String.split(@source, "\n", parts: 2) do
               ["# " <> _heading, rest] -> String.trim_leading(rest)
               _ -> @source
             end)

  @page %Page{
    id: "about",
    title: "Technical Overview",
    description:
      "How Cure works: the design philosophy, the kernel-checked compiler " <>
        "pipeline, the dependent type system, first-class OTP concurrency, " <>
        "the standard library, and the tooling around them.",
    category: :about,
    category_title: "About",
    order: 1,
    body: MarkdownConverter.to_html(@markdown, @highlighters)
  }

  @doc """
  The `CureSite.Pages.Page` struct served at `/about`.

  Built at compile time; callers get a plain struct with the body
  already rendered to HTML.
  """
  @spec page() :: %Page{}
  def page, do: @page

  @doc """
  Absolute path of the repository document this page is rendered from.
  """
  @spec source_path() :: String.t()
  def source_path, do: @source_path
end
