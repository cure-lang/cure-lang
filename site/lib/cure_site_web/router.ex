defmodule CureSiteWeb.Router do
  use CureSiteWeb, :router

  pipeline :browser do
    plug(:accepts, ["html"])
    plug(:fetch_session)
    plug(:fetch_live_flash)
    plug(:put_root_layout, html: {CureSiteWeb.Layouts, :root})
    plug(:protect_from_forgery)
    plug(:put_secure_browser_headers)
  end

  pipeline :api do
    plug(:accepts, ["json"])
  end

  # `/.well-known/llms.txt` (and casing variants) take precedence
  # over the generic catch-all `noop` so LLM-oriented crawlers see
  # the document instead of a 204 No Content. Chrome DevTools and
  # similar probes still hit the catch-all underneath.
  scope "/.well-known", CureSiteWeb do
    get("/llms.txt", LlmsController, :index)
    get("/llm.txt", LlmsController, :index)
    get("/LLM.txt", LlmsController, :index)
    get("/LLMS.txt", LlmsController, :index)
  end

  scope "/.well-known" do
    get("/*path", CureSiteWeb.WellKnownController, :noop)
  end

  scope "/", CureSiteWeb do
    pipe_through(:browser)

    # Crawler discovery: served from the router so the absolute URLs
    # they emit reflect the live endpoint configuration. Both routes
    # take precedence over `priv/static/*` because `static_paths/0`
    # no longer lists `robots.txt`.
    get("/sitemap.xml", SitemapController, :index)
    get("/robots.txt", SitemapController, :robots)

    # `llms.txt` (https://llmstxt.org). Phoenix routes are case-
    # sensitive, so each casing variant the spec suggests gets its
    # own entry. All four funnel through `LlmsController.index/2`.
    get("/llms.txt", LlmsController, :index)
    get("/llm.txt", LlmsController, :index)
    get("/LLM.txt", LlmsController, :index)
    get("/LLMS.txt", LlmsController, :index)

    get("/", PageController, :home)
    get("/blog", BlogController, :index)
    get("/blog/:id", BlogController, :show)
    live("/playground", PlaygroundLive, :index)
    live("/repl", ErrorLive, :index)
    live("/errors/:status", ErrorLive, :index)

    # Auto-generated stdlib documentation (extracted from lib/std/*.cure
    # at compile time by `CureSite.Stdlib`). The old monolithic
    # `/standard-library` page redirects here for backward compatibility.
    get("/stdlib", StdlibController, :index)
    get("/stdlib/:module", StdlibController, :show)
    get("/standard-library", RedirectController, :to_stdlib)

    get("/:id", PageController, :show)
  end

  # Other scopes may use custom stacks.
  # scope "/api", CureSiteWeb do
  #   pipe_through :api
  # end
end
