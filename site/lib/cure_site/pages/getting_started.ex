defmodule CureSite.Pages.GettingStarted do
  @moduledoc """
  The `/getting-started` page, rendered from the language repository's canonical
  getting started guide (`docs/GETTING_STARTED.md`).

  Like `CureSite.Pages.TechnicalOverview`, this page has no markdown file under
  `priv/pages`. The document is maintained in the repository next to the compiler
  it describes, and the site reads it at compile time, so the "Your first project"
  guide stays in sync with the repository.
  """

  alias CureSite.MarkdownConverter
  alias CureSite.Pages.Page

  # Mirrors the `:highlighters` list `CureSite.Pages` hands to
  # NimblePublisher, so both rendering paths agree.
  @highlighters [:makeup_cure, :makeup_elixir, :makeup_erlang]

  # `__DIR__` is `<repo>/site/lib/cure_site/pages` and the document
  # lives in `<repo>/docs`.
  @source_path Path.expand("../../../../docs/GETTING_STARTED.md", __DIR__)
  @external_resource @source_path

  unless File.exists?(@source_path) do
    raise """
    #{@source_path} is missing.

    The site's /getting-started page is rendered from the language repository's
    Getting Started guide. Restore the document, or update
    CureSite.Pages.GettingStarted, before compiling the site.
    """
  end

  @source File.read!(@source_path)

  @markdown (case String.split(@source, "\n", parts: 2) do
               ["# " <> _heading, rest] -> String.trim_leading(rest)
               _ -> @source
             end)

  @page %Page{
    id: "getting-started",
    title: "Your first project",
    description:
      "Takes a new Cure project from an empty directory to a compiled, running, tested program.",
    category: :about,
    category_title: "About",
    order: 2,
    body: MarkdownConverter.to_html(@markdown, @highlighters)
  }

  @doc """
  The `CureSite.Pages.Page` struct served at `/getting-started`.

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
