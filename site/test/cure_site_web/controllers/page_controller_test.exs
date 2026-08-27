defmodule CureSiteWeb.PageControllerTest do
  use CureSiteWeb.ConnCase

  test "GET / renders the home page with the dynamic Cure version", %{conn: conn} do
    conn = get(conn, ~p"/")
    body = html_response(conn, 200)

    assert body =~ "one dependent compiler pipeline"
    assert body =~ "kernel checking"
    refute body =~ "refinements"

    # Version is injected from the top-level mix.exs at compile time and
    # rendered in the navbar badge.
    version = CureSite.cure_version()
    assert body =~ "v" <> version

    # Top-level nav entries after the site rework.
    assert body =~ ~r{>\s*Learn\s*<}
    assert body =~ ~r{>\s*Concurrency\s*<}
    assert body =~ ~r{>\s*Stdlib\s*<}
    assert body =~ ~r{>\s*Tooling\s*<}
    assert body =~ ~r{>\s*Blog\s*<}
    assert body =~ ~r{>\s*About\s*<}

    # The About entry points at the page rendered from
    # `docs/TECHNICAL_OVERVIEW.md`.
    assert body =~ ~s(href="/about")
  end

  test "GET /about renders the repository technical overview", %{conn: conn} do
    conn = get(conn, ~p"/about")
    body = html_response(conn, 200)

    assert body =~ "Technical Overview"
    assert body =~ "Design Philosophy"
    assert body =~ "The Compiler Pipeline"

    # The nav entry is highlighted as the active one.
    assert body =~ ~r{<a href="/about" class="[^"]*btn-active[^"]*">\s*About\s*</a>}

    # `AboutPage` is the Schema.org type inferred for this page.
    assert body =~ ~s("@type":"AboutPage")
  end
end
