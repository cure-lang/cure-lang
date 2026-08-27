defmodule CureSiteWeb.JsonLd do
  @moduledoc """
  Build Schema.org JSON-LD payloads for every kind of page rendered
  by the site.

  Type inference reflects the actual content the visitor lands on:

    * `/`                               -> `SoftwareApplication`
      (the Cure language plus a `WebSite` + `Organization` baseline)
    * `/blog`                           -> `Blog` listing every post
    * `/blog/<id>`                      -> `TechArticle` with author,
      `datePublished`, and the post's tag list as `keywords`
    * `/stdlib`                         -> `CollectionPage` whose
      `mainEntity` is an `ItemList` of every `APIReference`
    * `/stdlib/<module>`                -> `APIReference` describing
      the Cure module with `programmingLanguage` and
      `targetPlatform` set
    * `priv/pages/getting-started.md`   -> `HowTo` whose `step` list
      is extracted from the page's `<h2>` headings
    * `/about` (`docs/TECHNICAL_OVERVIEW.md`) -> `AboutPage`
    * a markdown page whose body looks like a Q/A list -> `FAQPage`
      with each `<h2>`/`<h3>` ending in `?` lifted into a Question
    * every other markdown page         -> `TechArticle`
    * `/playground`                     -> `WebApplication`
    * `/repl` and error pages           -> `WebPage`

  Every page also carries a baseline `WebSite` and `Organization`
  schema so search engines have a stable identity record regardless
  of the entry point. The baseline is inserted automatically by the
  shared root layout via `entries/1`.

  ### Where the data comes from

    * `CureSiteWeb.Endpoint.url/0` -- canonical site URL, so the
      schemas reflect dev (`http://localhost:4000`), staging, or
      prod (`https://<PHX_HOST>`) without any code changes.
    * `Cure.version/0` -- version pinned in the umbrella `mix.exs`,
      flowed through `CureSite.cure_version/0`.
    * `CureSite.Pages`, `CureSite.Blog`, `CureSite.Stdlib` -- the
      same compile-time bundles the controllers and sitemap already
      use.
  """

  alias CureSite.Blog.Post
  alias CureSite.Pages.Page
  alias CureSiteWeb.Endpoint

  @typedoc "A `CureSite.Pages.Page` struct."
  @type page :: %Page{}

  @typedoc "A `CureSite.Blog.Post` struct."
  @type post :: %Post{}

  @typedoc "A Cure stdlib module documentation map (see `CureSite.Stdlib`)."
  @type stdlib_module :: %{required(:module) => String.t(), optional(any()) => any()}

  @site_name "Cure"
  @site_tagline "Cure — Dependently-Typed BEAM Language"
  @site_description "Dependently typed programming for the BEAM through one kernel-checked compiler pipeline."
  @logo_path "/images/logo-128x128-nobg.png"
  @repo_url "https://github.com/cure-lang/cure-lang"
  @license_url "https://github.com/cure-lang/cure-lang/blob/main/LICENSE"

  # Page IDs that should be treated as step-by-step how-to articles
  # rather than reference articles. Add new HowTo pages here as they
  # appear under `priv/pages/`.
  @howto_ids ~w(getting-started)

  # Page IDs that describe the project itself rather than a single
  # technical topic. Schema.org's `AboutPage` is the closest match and
  # tells crawlers this is the canonical "what is this" document.
  @about_ids ~w(about)

  # ---------------------------------------------------------------------------
  # Public API
  # ---------------------------------------------------------------------------

  @doc """
  Return the list of JSON-LD entries (already JSON-encoded strings)
  that should be embedded as `<script type="application/ld+json">`
  blocks for the current request.

  `assigns` may carry a `:json_ld` key with either a single Schema.org
  map or a list of maps. Anything else is ignored. The baseline pair
  (`WebSite` + `Organization`) is always prepended.
  """
  @spec entries(map() | keyword()) :: [String.t()]
  def entries(assigns) do
    extras =
      assigns
      |> get(:json_ld)
      |> List.wrap()
      |> Enum.filter(&is_map/1)

    (baseline() ++ extras)
    |> Enum.map(&encode/1)
  end

  @doc "Schema for the home page (`/`)."
  @spec for_home(String.t()) :: map()
  def for_home(version) do
    base = base_url()

    %{
      "@context" => "https://schema.org",
      "@type" => "SoftwareApplication",
      "@id" => base <> "/#cure",
      "name" => @site_name,
      "alternateName" => @site_tagline,
      "applicationCategory" => "DeveloperApplication",
      "applicationSubCategory" => "Programming Language",
      "operatingSystem" => "BEAM (Erlang VM)",
      "softwareVersion" => version,
      "programmingLanguage" => "Cure",
      "url" => base,
      "image" => base <> @logo_path,
      "logo" => base <> @logo_path,
      "description" => @site_description,
      "license" => @license_url,
      "codeRepository" => @repo_url,
      "audience" => %{"@type" => "Audience", "audienceType" => "Developer"},
      "offers" => %{
        "@type" => "Offer",
        "price" => "0",
        "priceCurrency" => "USD",
        "availability" => "https://schema.org/InStock"
      },
      "isPartOf" => %{"@id" => base <> "/#website"}
    }
  end

  @doc "Schema for an individual markdown page rendered at `/<id>`."
  @spec for_page(page()) :: map()
  def for_page(%Page{} = page) do
    base = base_url()
    canonical = base <> "/" <> page.id
    type = infer_page_type(page)

    common = %{
      "@context" => "https://schema.org",
      "@type" => type,
      "headline" => page.title,
      "name" => page.title,
      "description" => page.description,
      "url" => canonical,
      "mainEntityOfPage" => canonical,
      "inLanguage" => "en",
      "image" => base <> @logo_path,
      "isPartOf" => %{"@id" => base <> "/#website"},
      "publisher" => %{"@id" => base <> "/#organization"}
    }

    augment_for_type(common, type, page)
  end

  @doc "Schema for the blog listing at `/blog`."
  @spec for_blog_index([post()]) :: map()
  def for_blog_index(posts) do
    base = base_url()

    items =
      Enum.map(posts, fn %Post{} = post ->
        %{
          "@type" => "BlogPosting",
          "headline" => post.title,
          "name" => post.title,
          "description" => post.description,
          "datePublished" => Date.to_iso8601(post.date),
          "url" => base <> "/blog/" <> post.id,
          "author" => %{"@type" => "Person", "name" => post.author},
          "keywords" => Enum.join(post.tags, ", ")
        }
      end)

    %{
      "@context" => "https://schema.org",
      "@type" => "Blog",
      "name" => "Cure Blog",
      "url" => base <> "/blog",
      "description" => "Release notes, design notes, and walkthroughs for the Cure language.",
      "inLanguage" => "en",
      "publisher" => %{"@id" => base <> "/#organization"},
      "blogPost" => items
    }
  end

  @doc "Schema for an individual blog post at `/blog/<id>`."
  @spec for_blog_post(post()) :: map()
  def for_blog_post(%Post{} = post) do
    base = base_url()
    canonical = base <> "/blog/" <> post.id

    %{
      "@context" => "https://schema.org",
      "@type" => "TechArticle",
      "headline" => post.title,
      "name" => post.title,
      "description" => post.description,
      "datePublished" => Date.to_iso8601(post.date),
      "dateModified" => Date.to_iso8601(post.date),
      "url" => canonical,
      "mainEntityOfPage" => canonical,
      "inLanguage" => "en",
      "image" => base <> @logo_path,
      "keywords" => Enum.join(post.tags, ", "),
      "articleSection" => "Blog",
      "author" => %{"@type" => "Person", "name" => post.author},
      "publisher" => %{"@id" => base <> "/#organization"},
      "isPartOf" => %{"@id" => base <> "/#website"},
      "proficiencyLevel" => "Expert",
      "dependencies" => "Cure compiler, BEAM (Erlang VM)"
    }
  end

  @doc "Schema for the stdlib index at `/stdlib`."
  @spec for_stdlib_index([stdlib_module()]) :: map()
  def for_stdlib_index(modules) do
    base = base_url()

    items =
      modules
      |> Enum.with_index(1)
      |> Enum.map(fn {mod, idx} ->
        %{
          "@type" => "ListItem",
          "position" => idx,
          "url" => base <> "/stdlib/" <> mod.module,
          "name" => mod.module
        }
      end)

    %{
      "@context" => "https://schema.org",
      "@type" => "CollectionPage",
      "name" => "Cure Standard Library",
      "url" => base <> "/stdlib",
      "description" => "API reference for every module in the Cure standard library.",
      "inLanguage" => "en",
      "isPartOf" => %{"@id" => base <> "/#website"},
      "publisher" => %{"@id" => base <> "/#organization"},
      "mainEntity" => %{
        "@type" => "ItemList",
        "numberOfItems" => length(items),
        "itemListElement" => items
      }
    }
  end

  @doc "Schema for a single stdlib module at `/stdlib/<module>`."
  @spec for_stdlib_module(stdlib_module()) :: map()
  def for_stdlib_module(module_doc) do
    base = base_url()
    name = Map.get(module_doc, :module, "Std")
    canonical = base <> "/stdlib/" <> name

    %{
      "@context" => "https://schema.org",
      "@type" => "APIReference",
      "name" => name,
      "headline" => name,
      "description" => describe_stdlib_module(module_doc),
      "url" => canonical,
      "mainEntityOfPage" => canonical,
      "inLanguage" => "en",
      "image" => base <> @logo_path,
      "programmingLanguage" => "Cure",
      "targetPlatform" => "BEAM (Erlang VM)",
      "documentationVersion" => safe_cure_version(),
      "audience" => %{"@type" => "Audience", "audienceType" => "Developer"},
      "isPartOf" => %{"@id" => base <> "/#website"},
      "publisher" => %{"@id" => base <> "/#organization"}
    }
  end

  @doc "Schema for the interactive playground LiveView."
  @spec for_playground() :: map()
  def for_playground do
    base = base_url()

    %{
      "@context" => "https://schema.org",
      "@type" => "WebApplication",
      "name" => "Cure Playground",
      "applicationCategory" => "DeveloperApplication",
      "browserRequirements" => "Requires JavaScript and WebSockets.",
      "url" => base <> "/playground",
      "description" =>
        "Two-pane editor with live syntax highlighting and bidirectional type-checking, " <>
          "plus a sandboxed evaluator for one-shot runs.",
      "operatingSystem" => "Any (browser)",
      "inLanguage" => "en",
      "isPartOf" => %{"@id" => base <> "/#website"},
      "publisher" => %{"@id" => base <> "/#organization"},
      "offers" => %{
        "@type" => "Offer",
        "price" => "0",
        "priceCurrency" => "USD"
      }
    }
  end

  @doc "Schema for the in-browser REPL LiveView."
  @spec for_repl() :: map()
  def for_repl do
    base = base_url()

    %{
      "@context" => "https://schema.org",
      "@type" => "WebApplication",
      "name" => "Cure REPL",
      "applicationCategory" => "DeveloperApplication",
      "browserRequirements" => "Requires JavaScript and WebSockets.",
      "url" => base <> "/repl",
      "description" => "Browser-based access to the Cure interactive REPL.",
      "operatingSystem" => "Any (browser)",
      "inLanguage" => "en",
      "isPartOf" => %{"@id" => base <> "/#website"},
      "publisher" => %{"@id" => base <> "/#organization"}
    }
  end

  @doc "Schema for an HTTP error page (404, 500, etc)."
  @spec for_error(integer()) :: map()
  def for_error(status) when is_integer(status) do
    base = base_url()

    %{
      "@context" => "https://schema.org",
      "@type" => "WebPage",
      "name" => "Cure — HTTP #{status}",
      "url" => base <> "/errors/#{status}",
      "description" => "HTTP #{status} response from cure-lang.",
      "inLanguage" => "en",
      "isPartOf" => %{"@id" => base <> "/#website"},
      "publisher" => %{"@id" => base <> "/#organization"}
    }
  end

  # ---------------------------------------------------------------------------
  # Internals
  # ---------------------------------------------------------------------------

  # `WebSite` + `Organization` records that always appear on every
  # page. The fragment-IDs (`#website`, `#organization`) let the
  # per-page schemas reference them via `@id` without duplicating
  # their fields.
  defp baseline do
    base = base_url()

    [
      %{
        "@context" => "https://schema.org",
        "@type" => "WebSite",
        "@id" => base <> "/#website",
        "url" => base,
        "name" => @site_name,
        "alternateName" => @site_tagline,
        "description" => @site_description,
        "inLanguage" => "en",
        "publisher" => %{"@id" => base <> "/#organization"},
        "potentialAction" => %{
          "@type" => "SearchAction",
          "target" => %{
            "@type" => "EntryPoint",
            "urlTemplate" => base <> "/stdlib?q={search_term_string}"
          },
          "query-input" => "required name=search_term_string"
        }
      },
      %{
        "@context" => "https://schema.org",
        "@type" => "Organization",
        "@id" => base <> "/#organization",
        "name" => @site_name,
        "url" => base,
        "logo" => base <> @logo_path,
        "sameAs" => [@repo_url]
      }
    ]
  end

  defp encode(map), do: Jason.encode!(map, escape: :html_safe)

  defp base_url do
    Endpoint.url() |> String.trim_trailing("/")
  rescue
    # The Endpoint may not have started during certain compile-time
    # paths (doctests, mix tasks). Fall back to a relative origin so
    # the schemas never crash a render. Any non-runtime path will be
    # ignored by crawlers anyway.
    _ -> ""
  end

  defp safe_cure_version do
    if function_exported?(Cure, :version, 0), do: Cure.version(), else: "unknown"
  end

  defp get(assigns, key) when is_map(assigns), do: Map.get(assigns, key)
  defp get(assigns, key) when is_list(assigns), do: Keyword.get(assigns, key)
  defp get(_, _), do: nil

  # --- type inference --------------------------------------------------------

  defp infer_page_type(%Page{id: id}) when id in @howto_ids, do: "HowTo"
  defp infer_page_type(%Page{id: id}) when id in @about_ids, do: "AboutPage"

  defp infer_page_type(%Page{body: body}) when is_binary(body) do
    if faq_page?(body), do: "FAQPage", else: "TechArticle"
  end

  defp infer_page_type(_), do: "TechArticle"

  # A page is treated as an FAQ when at least three of its `<h2>` or
  # `<h3>` headings end in a question mark. This mirrors how a human
  # reader would categorise the page and matches Google's own
  # FAQPage rich-result requirements.
  defp faq_page?(html_body) do
    ~r/<h[23][^>]*>([^<]*\?)\s*<\/h[23]>/i
    |> Regex.scan(html_body, capture: :all_but_first)
    |> length()
    |> Kernel.>=(3)
  end

  defp augment_for_type(map, "HowTo", %Page{body: body}) do
    case parse_steps(body) do
      [] -> map
      steps -> Map.put(map, "step", steps)
    end
  end

  defp augment_for_type(map, "FAQPage", %Page{body: body}) do
    case parse_faq_questions(body) do
      [] -> map
      qs -> Map.put(map, "mainEntity", qs)
    end
  end

  defp augment_for_type(map, _type, _page), do: map

  # Lift each `<h2>` heading into a HowToStep. We deliberately stop
  # at H2 because deeper headings frequently describe sub-topics
  # within a step rather than separate steps in their own right.
  defp parse_steps(html_body) when is_binary(html_body) do
    ~r/<h2[^>]*>([^<]+)<\/h2>/i
    |> Regex.scan(html_body, capture: :all_but_first)
    |> List.flatten()
    |> Enum.with_index(1)
    |> Enum.map(fn {name, idx} ->
      %{
        "@type" => "HowToStep",
        "position" => idx,
        "name" => name |> String.trim() |> normalise_whitespace()
      }
    end)
  end

  defp parse_steps(_), do: []

  defp parse_faq_questions(html_body) when is_binary(html_body) do
    ~r/<h[23][^>]*>([^<]*\?)\s*<\/h[23]>/i
    |> Regex.scan(html_body, capture: :all_but_first)
    |> List.flatten()
    |> Enum.map(fn raw ->
      %{
        "@type" => "Question",
        "name" => raw |> String.trim() |> normalise_whitespace(),
        "acceptedAnswer" => %{
          "@type" => "Answer",
          "text" => "See the page body for the full answer."
        }
      }
    end)
  end

  defp parse_faq_questions(_), do: []

  # --- helpers --------------------------------------------------------------

  defp describe_stdlib_module(%{module_doc: doc}) when is_binary(doc) and doc != "" do
    doc
    |> String.split(~r/\n{2,}/, parts: 2)
    |> List.first("")
    |> String.trim()
    |> normalise_whitespace()
    |> truncate(360)
    |> case do
      "" -> "API reference for the Cure standard library."
      text -> text
    end
  end

  defp describe_stdlib_module(%{module: name}),
    do: "API reference for the Cure standard library module #{name}."

  defp describe_stdlib_module(_), do: "API reference for the Cure standard library."

  defp normalise_whitespace(text) do
    text
    |> String.replace(~r/\s+/u, " ")
    |> String.trim()
  end

  defp truncate(text, max) when byte_size(text) <= max, do: text

  defp truncate(text, max) do
    text
    |> String.slice(0, max - 1)
    |> Kernel.<>("…")
  end
end
