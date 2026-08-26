defmodule CureSiteWeb.LlmsControllerTest do
  use CureSiteWeb.ConnCase, async: true

  alias CureSite.{Blog, Pages, Stdlib}

  @paths [
    "/llms.txt",
    "/llm.txt",
    "/LLM.txt",
    "/LLMS.txt",
    "/.well-known/llms.txt",
    "/.well-known/llm.txt",
    "/.well-known/LLM.txt",
    "/.well-known/LLMS.txt"
  ]

  describe "every advertised path serves the same llms.txt" do
    test "all eight routes return identical text/plain bodies", %{conn: conn} do
      bodies =
        Enum.map(@paths, fn path ->
          response = get(conn, path)
          assert response.status == 200, "expected 200 for #{path}, got #{response.status}"
          assert response_content_type(response, :txt) =~ "text/plain"
          response(response, 200)
        end)

      [first | rest] = bodies

      Enum.each(Enum.zip(@paths -- [List.first(@paths)], rest), fn {path, body} ->
        assert body == first,
               "body for #{path} diverges from /llms.txt"
      end)
    end

    test "each path is also enumerated in the documentation order it appears here" do
      # Sanity check: the canonical path comes first so direct-match
      # crawlers (the spec's recommended target) hit the most common
      # variant without re-routing.
      assert hd(@paths) == "/llms.txt"
    end
  end

  describe "document structure" do
    test "starts with a Markdown title, blockquote summary and free-form context", %{conn: conn} do
      body = get(conn, "/llms.txt") |> response(200)

      [first_line, second_line | _rest] = String.split(body, "\n")

      assert String.starts_with?(first_line, "# Cure v")
      assert String.starts_with?(second_line, "> Dependently typed programming")
      assert body =~ "Every program follows the same dependent pipeline"
      assert body =~ "independent kernel checking"
      refute body =~ "SMT-backed verification"
    end

    test "lists every page under the Documentation section", %{conn: conn} do
      body = get(conn, "/llms.txt") |> response(200)

      assert body =~ "## Documentation"

      for page <- Pages.all_pages() do
        assert body =~ "(#{base_url()}/#{page.id})",
               "expected /#{page.id} link in llms.txt"

        assert body =~ "[#{page.title}](",
               "expected #{page.title} title in llms.txt"
      end
    end

    test "lists every blog post under the Blog section with publication date", %{conn: conn} do
      body = get(conn, "/llms.txt") |> response(200)

      assert body =~ "## Blog"

      for post <- Blog.all_posts() do
        assert body =~ "(#{base_url()}/blog/#{post.id})"
        assert body =~ Date.to_iso8601(post.date)
      end
    end

    test "lists every stdlib module under the Standard Library section", %{conn: conn} do
      body = get(conn, "/llms.txt") |> response(200)

      assert body =~ "## Standard Library"

      for mod <- Stdlib.modules() do
        assert body =~ "(#{base_url()}/stdlib/#{mod.module})"
        assert body =~ "[#{mod.module}]"
      end
    end

    test "advertises the playground/REPL surfaces, sitemap, robots and source repo", %{conn: conn} do
      body = get(conn, "/llms.txt") |> response(200)

      assert body =~ "[Playground](#{base_url()}/playground)"
      assert body =~ "[REPL](#{base_url()}/repl)"
      assert body =~ "[Sitemap](#{base_url()}/sitemap.xml)"
      assert body =~ "[Robots](#{base_url()}/robots.txt)"
      assert body =~ "[Source repository](https://github.com/cure-lang/cure-lang)"
      assert body =~ "[Macro language](https://hexdocs.pm/cure/macros.html)"
      assert body =~ "[Proof authoring](https://hexdocs.pm/cure/proofs.html)"
    end

    test "the .well-known variant is byte-identical with the root variant", %{conn: conn} do
      root = get(conn, "/llms.txt") |> response(200)
      well_known = get(conn, "/.well-known/llms.txt") |> response(200)

      assert root == well_known
    end
  end

  describe "casing variants" do
    test "uppercase paths still route through the same controller", %{conn: conn} do
      response = get(conn, "/LLMS.txt")
      assert response.status == 200
      body = response(response, 200)
      assert body =~ "## Documentation"
    end

    test "/.well-known/LLM.txt resolves before the /.well-known catch-all", %{conn: conn} do
      response = get(conn, "/.well-known/LLM.txt")
      # If the catch-all had won we'd see 204 and an empty body.
      assert response.status == 200
      assert response(response, 200) =~ "# Cure v"
    end
  end

  # ---------------------------------------------------------------------------

  defp base_url do
    String.trim_trailing(CureSiteWeb.Endpoint.url(), "/")
  end
end
