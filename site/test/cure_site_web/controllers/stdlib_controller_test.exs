defmodule CureSiteWeb.StdlibControllerTest do
  use CureSiteWeb.ConnCase, async: true

  test "GET /stdlib renders the index with all module groups", %{conn: conn} do
    conn = get(conn, ~p"/stdlib")
    assert html_response(conn, 200) =~ "Standard Library"
    assert html_response(conn, 200) =~ "Core &amp; Type System"
    assert html_response(conn, 200) =~ "Proofs &amp; Formal Verification"
    assert html_response(conn, 200) =~ "Std.Core"
  end

  test "GET /stdlib/:module renders module show page", %{conn: conn} do
    conn = get(conn, ~p"/stdlib/Std.Core")
    assert html_response(conn, 200) =~ "Std.Core"
    assert html_response(conn, 200) =~ "View source"
  end

  test "GET /stdlib/:module returns 404 for unknown module", %{conn: conn} do
    conn = get(conn, ~p"/stdlib/Std.UnknownModule")
    assert html_response(conn, 404) =~ "Page not found"
  end
end
