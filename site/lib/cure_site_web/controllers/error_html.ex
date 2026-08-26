defmodule CureSiteWeb.ErrorHTML do
  @moduledoc """
  Renders HTML error pages (404, 5xx).

  Each template embeds a `CureSiteWeb.ErrorLive` LiveView so visitors get a
  live Cure REPL terminal even on error pages.
  """
  use CureSiteWeb, :html

  embed_templates("error_html/*")
end
