defmodule CureSiteWeb.Layouts do
  @moduledoc """
  This module holds layouts and related functionality
  used by your application.
  """
  use CureSiteWeb, :html

  # Embed all files in layouts/* within this module.
  # The default root.html.heex file contains the HTML
  # skeleton of your application, namely HTML headers
  # and other static content.
  embed_templates("layouts/*")

  @doc """
  Renders your app layout.

  This function is typically invoked from every template,
  and it often contains your application menu, sidebar,
  or similar.

  ## Examples

      <Layouts.app flash={@flash}>
        <h1>Content</h1>
      </Layouts.app>

  """
  attr(:flash, :map, required: true, doc: "the map of flash messages")

  attr(:current_scope, :map,
    default: nil,
    doc: "the current [scope](https://hexdocs.pm/phoenix/scopes.html)"
  )

  attr(:current_path, :string,
    default: "",
    doc: "the current request path, used to highlight the active navbar entry"
  )

  slot(:inner_block, required: true)

  def app(assigns) do
    assigns = assign(assigns, :cure_version, CureSite.cure_version())

    ~H"""
    <header class="sticky top-0 z-50 border-b border-base-300 bg-base-100/95 backdrop-blur">
      <nav class="mx-auto flex max-w-6xl items-center justify-between px-4 py-3 sm:px-6">
        <a href="/" class="flex items-center gap-2">
          <img src={~p"/images/logo-128x128-nobg.png"} width="32" height="32" alt="Cure" />
          <span class="text-lg font-bold tracking-tight">Cure</span>
          <span class="badge badge-xs badge-primary font-mono" title="Current Cure language version">
            v{@cure_version}
          </span>
        </a>

        <div class="hidden items-center gap-1 md:flex">
          <a href={~p"/about"} class={nav_class(@current_path, :about)}>
            About
          </a>
          <a href={~p"/tour"} class={nav_class(@current_path, :learn)}>
            Learn
          </a>
          <a href={~p"/actors"} class={nav_class(@current_path, :concurrency)}>
            Concurrency
          </a>
          <a href={~p"/stdlib"} class={nav_class(@current_path, :stdlib)}>
            Stdlib
          </a>
          <a href={~p"/tooling"} class={nav_class(@current_path, :tooling)}>
            Tooling
          </a>
          <a href={~p"/blog"} class={nav_class(@current_path, :blog)}>
            Blog
          </a>
          <.theme_toggle />
        </div>

        <%!-- Mobile menu button --%>
        <div class="flex items-center gap-2 md:hidden">
          <.theme_toggle />
          <button
            class="btn btn-ghost btn-sm"
            onclick="document.getElementById('mobile-menu').classList.toggle('hidden')"
          >
            <.icon name="hero-bars-3" class="size-5" />
          </button>
        </div>
      </nav>

      <%!-- Mobile navigation --%>
      <div id="mobile-menu" class="hidden border-t border-base-300 px-4 py-3 md:hidden space-y-2">
        <div>
          <div class="text-xs font-semibold uppercase tracking-wider text-base-content/50 mb-1">
            About
          </div>
          <div class="pl-2 space-y-1">
            <a href={~p"/about"} class={mobile_nav_class(@current_path, ~p"/about")}>
              Technical Overview
            </a>
            <a
              href={~p"/getting-started"}
              class={mobile_nav_class(@current_path, ~p"/getting-started")}
            >
              Your First Project
            </a>
            <a
              href={~p"/escrow-exchange"}
              class={mobile_nav_class(@current_path, ~p"/escrow-exchange")}
            >
              Escrew&Exchange project
            </a>
          </div>
        </div>

        <div>
          <div class="text-xs font-semibold uppercase tracking-wider text-base-content/50 mb-1">
            Learn Cure
          </div>
          <div class="pl-2 space-y-1">
            <a href={~p"/tour"} class={mobile_nav_class(@current_path, ~p"/tour")}>
              Language Tour
            </a>
            <a href={~p"/language-guide"} class={mobile_nav_class(@current_path, ~p"/language-guide")}>
              Language Guide
            </a>
            <a href={~p"/match"} class={mobile_nav_class(@current_path, ~p"/match")}>
              Pattern Matching
            </a>
            <a href={~p"/pickup"} class={mobile_nav_class(@current_path, ~p"/pickup")}>
              Conditional Dispatch
            </a>
            <a href={~p"/type-system"} class={mobile_nav_class(@current_path, ~p"/type-system")}>
              Type System
            </a>
            <a href={~p"/protocols"} class={mobile_nav_class(@current_path, ~p"/protocols")}>
              Interfaces & Protocols
            </a>
          </div>
        </div>

        <div>
          <div class="text-xs font-semibold uppercase tracking-wider text-base-content/50 mb-1">
            OTP & Concurrency
          </div>
          <div class="pl-2 space-y-1">
            <a href={~p"/actors"} class={mobile_nav_class(@current_path, ~p"/actors")}>
              Actors & Supervision
            </a>
            <a
              href={~p"/finite-state-machines"}
              class={mobile_nav_class(@current_path, ~p"/finite-state-machines")}
            >
              Finite State Machines
            </a>
            <a href={~p"/applications"} class={mobile_nav_class(@current_path, ~p"/applications")}>
              Applications & Releases
            </a>
          </div>
        </div>

        <div>
          <div class="text-xs font-semibold uppercase tracking-wider text-base-content/50 mb-1">
            Ecosystem
          </div>
          <div class="pl-2 space-y-1">
            <a href={~p"/stdlib"} class={mobile_nav_class(@current_path, ~p"/stdlib")}>
              Standard Library
            </a>
            <a href={~p"/tooling"} class={mobile_nav_class(@current_path, ~p"/tooling")}>
              Tooling
            </a>
            <a href={~p"/repl"} class={mobile_nav_class(@current_path, ~p"/repl")}>
              REPL Reference
            </a>
            <a href={~p"/roadmap"} class={mobile_nav_class(@current_path, ~p"/roadmap")}>
              Roadmap
            </a>
            <a href={~p"/blog"} class={mobile_nav_class(@current_path, ~p"/blog")}>
              Blog
            </a>
          </div>
        </div>

        <div>
          <div class="text-xs font-semibold uppercase tracking-wider text-base-content/50 mb-1">
            About
          </div>
          <div class="pl-2 space-y-1">
            <a href={~p"/about"} class={mobile_nav_class(@current_path, ~p"/about")}>
              Technical Overview
            </a>
          </div>
        </div>
      </div>
    </header>

    <main class="mx-auto max-w-6xl px-4 py-10 sm:px-6 lg:px-8">
      {render_slot(@inner_block)}
    </main>

    <footer class="border-t border-base-300 mt-16">
      <div class="mx-auto max-w-6xl px-4 py-8 sm:px-6">
        <div class="flex flex-col items-center justify-between gap-4 sm:flex-row">
          <div class="flex items-center gap-4 text-sm text-base-content/60">
            <a href="https://github.com/cure-lang/cure-lang" class="hover:text-base-content">
              GitHub
            </a>
            <a href={~p"/getting-started"} class="hover:text-base-content">Getting Started</a>
            <a href={~p"/roadmap"} class="hover:text-base-content">Roadmap</a>
          </div>
          <p class="text-xs text-base-content/40">Cure v{@cure_version} -- Aleksei Matiushkin</p>
        </div>
      </div>
    </footer>

    <.flash_group flash={@flash} />
    """
  end

  @doc """
  Shows the flash group with standard titles and content.

  ## Examples

      <.flash_group flash={@flash} />
  """
  attr(:flash, :map, required: true, doc: "the map of flash messages")
  attr(:id, :string, default: "flash-group", doc: "the optional id of flash container")

  def flash_group(assigns) do
    ~H"""
    <div id={@id} aria-live="polite">
      <.flash kind={:info} flash={@flash} />
      <.flash kind={:error} flash={@flash} />
    </div>
    """
  end

  @doc """
  Provides dark vs light theme toggle based on themes defined in app.css.

  See <head> in root.html.heex which applies the theme before page load.
  """
  def theme_toggle(assigns) do
    ~H"""
    <div class="card relative flex flex-row items-center border-2 border-base-300 bg-base-300 rounded-full">
      <div class="absolute w-1/3 h-full rounded-full border-1 border-base-200 bg-base-100 brightness-200 left-0 [[data-theme=light]_&]:left-1/3 [[data-theme=dark]_&]:left-2/3 transition-[left]" />

      <button
        class="flex p-2 cursor-pointer w-1/3"
        data-phx-theme="system"
      >
        <.icon name="hero-computer-desktop-micro" class="size-4 opacity-75 hover:opacity-100" />
      </button>

      <button
        class="flex p-2 cursor-pointer w-1/3"
        data-phx-theme="light"
      >
        <.icon name="hero-sun-micro" class="size-4 opacity-75 hover:opacity-100" />
      </button>

      <button
        class="flex p-2 cursor-pointer w-1/3"
        data-phx-theme="dark"
      >
        <.icon name="hero-moon-micro" class="size-4 opacity-75 hover:opacity-100" />
      </button>
    </div>
    """
  end

  # ------------------------------------------------------------
  # Navigation highlighting helpers
  # ------------------------------------------------------------

  @desktop_base "btn btn-ghost btn-sm"
  @desktop_active "btn btn-sm btn-active bg-base-200 text-primary font-semibold"
  @mobile_base "block py-1.5 text-sm"
  @mobile_active "block py-1.5 text-sm text-primary font-semibold"

  @doc false
  def nav_class(current_path, target) when is_atom(target) do
    if active_category?(current_path, target), do: @desktop_active, else: @desktop_base
  end

  def nav_class(current_path, target) do
    if active_link?(current_path, target), do: @desktop_active, else: @desktop_base
  end

  @doc false
  def mobile_nav_class(current_path, target) do
    if active_link?(current_path, target), do: @mobile_active, else: @mobile_base
  end

  defp active_category?(current, :learn) do
    current in [
      "/tour",
      "/language-guide",
      "/match",
      "/pickup",
      "/type-system",
      "/protocols"
    ]
  end

  defp active_category?(current, :concurrency) do
    current in ["/actors", "/finite-state-machines", "/applications"]
  end

  defp active_category?(current, :tooling) do
    current in ["/tooling", "/repl", "/playground"]
  end

  defp active_category?(current, :stdlib) do
    String.starts_with?(current, "/stdlib") or String.starts_with?(current, "/standard-library")
  end

  defp active_category?(current, :blog) do
    String.starts_with?(current, "/blog")
  end

  defp active_category?(current, :about) do
    current in ["/about", "/getting-started"]
  end

  defp active_category?(_current, _target), do: false

  # A link is active when the current path matches the target exactly or,
  # for non-root targets, the current path sits under the target segment
  # (so /blog/some-post keeps the "Blog" entry highlighted).
  defp active_link?(current, target) when is_binary(current) and is_binary(target) do
    current == target or
      (target != "/" and String.starts_with?(current, target <> "/"))
  end

  defp active_link?(_current, _target), do: false
end
