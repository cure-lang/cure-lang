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
  end
end
