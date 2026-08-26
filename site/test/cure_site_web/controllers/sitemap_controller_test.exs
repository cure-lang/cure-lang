defmodule CureSiteWeb.SitemapControllerTest do
  use CureSiteWeb.ConnCase

  alias CureSite.{Blog, Pages, Stdlib}

  describe "GET /sitemap.xml" do
    test "advertises every category of indexable URL", %{conn: conn} do
      conn = get(conn, ~p"/sitemap.xml")

      assert response_content_type(conn, :xml) =~ "application/xml"
      body = response(conn, 200)

      assert body =~ ~s(<?xml version="1.0" encoding="UTF-8"?>)
      assert body =~ ~s(<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">)

      base = String.trim_trailing(CureSiteWeb.Endpoint.url(), "/")

      # Static landing pages and LiveViews exposed by the router.
      for path <- ~w(/ /blog /stdlib /playground /repl) do
        assert body =~ "<loc>#{base}#{path}</loc>",
               "expected #{path} in sitemap"
      end

      # Every markdown page under priv/pages is reachable via /:id.
      for page <- Pages.all_pages() do
        assert body =~ "<loc>#{base}/#{page.id}</loc>",
               "expected /#{page.id} in sitemap"
      end

      # Every blog post and stdlib module is enumerated.
      for post <- Blog.all_posts() do
        assert body =~ "<loc>#{base}/blog/#{post.id}</loc>"
        assert body =~ "<lastmod>#{Date.to_iso8601(post.date)}</lastmod>"
      end

      for mod <- Stdlib.modules() do
        assert body =~ "<loc>#{base}/stdlib/#{mod.module}</loc>"
      end
    end

    test "is well-formed XML with no duplicate <loc> entries", %{conn: conn} do
      conn = get(conn, ~p"/sitemap.xml")
      body = response(conn, 200)

      open = body |> String.split("<url>") |> length()
      close = body |> String.split("</url>") |> length()
      assert open == close, "mismatched <url>/</url> tags in sitemap"

      locs =
        ~r{<loc>([^<]+)</loc>}
        |> Regex.scan(body, capture: :all_but_first)
        |> List.flatten()

      assert locs == Enum.uniq(locs), "sitemap contains duplicate <loc> entries"
    end
  end

  describe "GET /robots.txt" do
    test "is served from the router and points at the absolute sitemap URL", %{conn: conn} do
      conn = get(conn, ~p"/robots.txt")

      assert response_content_type(conn, :txt) =~ "text/plain"
      body = response(conn, 200)

      base = String.trim_trailing(CureSiteWeb.Endpoint.url(), "/")
      assert body =~ "User-agent: *"
      assert body =~ "Allow: /"
      assert body =~ "Sitemap: #{base}/sitemap.xml"
    end
  end

  describe "every rendered page" do
    test "links the sitemap from <head>", %{conn: conn} do
      body =
        conn
        |> get(~p"/")
        |> html_response(200)

      assert body =~
               ~s(<link rel="sitemap" type="application/xml" title="Sitemap" href="/sitemap.xml")
    end
  end
end
