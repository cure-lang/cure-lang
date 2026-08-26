defmodule CureSiteWeb.SitemapController do
  @moduledoc """
  Serves a comprehensive XML sitemap at `/sitemap.xml` and a
  matching `/robots.txt` that points crawlers at it.

  The sitemap stitches together every URL the site genuinely renders:

    * the home page, the blog index, the stdlib index, the
      `playground`/`repl` LiveViews;
    * every entry in `priv/pages/*.md` plus the repository-sourced
      `/about` page (all served at `/:id` by
      `PageController.show/2`);
    * every blog post in `priv/posts/**/*.md` (served at `/blog/:id`
      by `BlogController.show/2`), with its publication date as
      `<lastmod>`;
    * every Cure stdlib module discovered at compile time by
      `CureSite.Stdlib` (served at `/stdlib/:module`).

  Routes that are pure redirects (`/standard-library`) or one-off
  diagnostics (`/errors/:status`, `/.well-known/*`) are intentionally
  excluded.

  All `<loc>` URLs are absolute and derived from the running endpoint
  via `CureSiteWeb.Endpoint.url/0` so the same controller produces a
  correct sitemap whether the host is `localhost:4000`, a staging
  domain, or `https://example.com`.
  """
  use CureSiteWeb, :controller

  alias CureSite.{Blog, Pages, Stdlib}
  alias CureSiteWeb.Endpoint

  # Routes exposed by `CureSiteWeb.Router` that don't have a backing
  # markdown file but are nevertheless valuable for crawlers. The tuple
  # shape is `{path, changefreq, priority}`; `<lastmod>` for these is
  # the build's release date so each redeploy bumps every entry.
  @static_routes [
    {"/", "weekly", "1.0"},
    {"/blog", "weekly", "0.8"},
    {"/stdlib", "weekly", "0.8"},
    {"/playground", "monthly", "0.6"},
    {"/repl", "monthly", "0.6"}
  ]

  @doc """
  Render the XML sitemap.
  """
  def index(conn, _params) do
    base = base_url()
    today = Date.to_iso8601(Date.utc_today())

    urls =
      [
        static_route_entries(today),
        page_entries(today),
        blog_entries(),
        stdlib_entries(today)
      ]
      |> Enum.concat()
      # Defensive dedupe: a markdown page with the same id as a live
      # route (e.g. `playground.md` + `live "/playground"`) is reachable
      # under one URL only, so collapse on the path before rendering.
      |> Enum.uniq_by(fn %{path: path} -> path end)

    body = render_sitemap(base, urls)

    conn
    |> put_resp_content_type("application/xml")
    |> send_resp(200, body)
  end

  @doc """
  Render a `robots.txt` that allows everything and advertises the
  sitemap with an absolute URL.
  """
  def robots(conn, _params) do
    base = base_url()

    body = """
    # See https://www.robotstxt.org/robotstxt.html for documentation
    # on how to use the robots.txt file.

    User-agent: *
    Allow: /

    Sitemap: #{base}/sitemap.xml
    """

    conn
    |> put_resp_content_type("text/plain")
    |> send_resp(200, body)
  end

  # ---------------------------------------------------------------------------
  # Entry builders
  # ---------------------------------------------------------------------------

  defp static_route_entries(today) do
    Enum.map(@static_routes, fn {path, changefreq, priority} ->
      %{path: path, lastmod: today, changefreq: changefreq, priority: priority}
    end)
  end

  defp page_entries(today) do
    Pages.all_pages()
    # Hidden / draft pages use `order: 0`; surface them anyway because
    # they remain reachable via direct URL, but down-rank them below
    # navigation pages.
    |> Enum.map(fn page ->
      %{
        path: "/" <> page.id,
        lastmod: today,
        changefreq: "monthly",
        priority: if(page.order > 0, do: "0.7", else: "0.4")
      }
    end)
  end

  defp blog_entries do
    Enum.map(Blog.all_posts(), fn post ->
      %{
        path: "/blog/" <> post.id,
        lastmod: Date.to_iso8601(post.date),
        changefreq: "yearly",
        priority: "0.6"
      }
    end)
  end

  defp stdlib_entries(today) do
    Enum.map(Stdlib.modules(), fn mod ->
      %{
        path: "/stdlib/" <> mod.module,
        lastmod: today,
        changefreq: "monthly",
        priority: "0.5"
      }
    end)
  end

  # ---------------------------------------------------------------------------
  # XML rendering
  # ---------------------------------------------------------------------------

  defp render_sitemap(base, urls) do
    body =
      Enum.map_join(urls, "\n", fn url ->
        loc = escape_xml(base <> url.path)

        """
          <url>
            <loc>#{loc}</loc>
            <lastmod>#{url.lastmod}</lastmod>
            <changefreq>#{url.changefreq}</changefreq>
            <priority>#{url.priority}</priority>
          </url>\
        """
      end)

    """
    <?xml version="1.0" encoding="UTF-8"?>
    <urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
    #{body}
    </urlset>
    """
  end

  defp base_url do
    Endpoint.url() |> String.trim_trailing("/")
  end

  defp escape_xml(value) do
    value
    |> String.replace("&", "&amp;")
    |> String.replace("<", "&lt;")
    |> String.replace(">", "&gt;")
    |> String.replace("\"", "&quot;")
    |> String.replace("'", "&apos;")
  end
end
