defmodule CureSite.Pages do
  alias CureSite.Pages.Page
  alias CureSite.Pages.TechnicalOverview

  use NimblePublisher,
    build: Page,
    from: Application.app_dir(:cure_site, "priv/pages/**/*.md"),
    as: :pages,
    highlighters: [:makeup_cure, :makeup_elixir, :makeup_erlang],
    html_converter: CureSite.MarkdownConverter

  # `/about` has no markdown file under `priv/pages`: it is the
  # repository's `docs/TECHNICAL_OVERVIEW.md`, rendered at compile time
  # by `CureSite.Pages.TechnicalOverview`. Merging it into `@pages`
  # here means the docs sidebar, prev/next navigation, `/sitemap.xml`
  # and `llms.txt` treat it exactly like an authored page.
  @pages Enum.sort_by([TechnicalOverview.page() | @pages], & &1.order)

  def all_pages, do: @pages

  def nav_pages do
    Enum.filter(all_pages(), &(&1.order > 0))
  end

  def categories do
    [
      {:about, "About", "What Cure is, how its compiler works, and why it is designed this way"},
      {:learn, "Learn Cure", "Language basics, syntax, patterns, and type system"},
      {:concurrency, "OTP & Concurrency",
       "Actors, state machines, supervision, and applications"},
      {:tooling, "Tooling & Ecosystem", "CLI, LSP, compiler events, profiler, and REPL"},
      {:roadmap, "Roadmap", "Language evolution and upcoming features"}
    ]
  end

  def pages_by_category(category) do
    all_pages()
    |> Enum.filter(&(&1.category == category))
    |> Enum.sort_by(& &1.order)
  end

  def grouped_pages do
    for {cat, title, desc} <- categories() do
      {cat, title, desc, pages_by_category(cat)}
    end
  end

  def prev_and_next(current_id) do
    # Flatten all ordered pages across categories
    ordered = Enum.flat_map(categories(), fn {cat, _, _} -> pages_by_category(cat) end)
    idx = Enum.find_index(ordered, &(&1.id == current_id))

    case idx do
      nil ->
        {nil, nil}

      i ->
        prev_page = if i > 0, do: Enum.at(ordered, i - 1), else: nil
        next_page = if i < length(ordered) - 1, do: Enum.at(ordered, i + 1), else: nil
        {prev_page, next_page}
    end
  end

  defmodule NotFoundError do
    defexception [:message, plug_status: 404]
  end

  def get_page_by_id!(id) do
    Enum.find(all_pages(), &(&1.id == id)) ||
      raise NotFoundError, "page with id=#{id} not found"
  end
end
