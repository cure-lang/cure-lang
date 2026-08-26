defmodule CureSiteWeb.JsonLdTest do
  use CureSiteWeb.ConnCase, async: true

  alias CureSite.{Blog, Pages, Stdlib}
  alias CureSiteWeb.JsonLd

  describe "entries/1" do
    test "always emits the WebSite + Organization baseline" do
      [website, org] =
        %{}
        |> JsonLd.entries()
        |> Enum.take(2)
        |> Enum.map(&Jason.decode!/1)

      assert website["@type"] == "WebSite"
      assert website["url"] != ""
      assert website["publisher"]["@id"] == website["@id"] |> ref_to_org()

      assert org["@type"] == "Organization"
      assert org["name"] == "Cure"
      assert "https://github.com/cure-lang/cure-lang" in org["sameAs"]
    end

    test "appends a single :json_ld assign as a third entry" do
      schema = %{"@context" => "https://schema.org", "@type" => "WebPage", "name" => "X"}
      assert [_baseline_a, _baseline_b, payload] = JsonLd.entries(%{json_ld: schema})

      decoded = Jason.decode!(payload)
      assert decoded["@type"] == "WebPage"
      assert decoded["name"] == "X"
    end

    test "appends every entry when :json_ld is a list" do
      a = %{"@context" => "https://schema.org", "@type" => "Thing", "name" => "A"}
      b = %{"@context" => "https://schema.org", "@type" => "Thing", "name" => "B"}

      decoded =
        %{json_ld: [a, b]}
        |> JsonLd.entries()
        |> Enum.drop(2)
        |> Enum.map(&Jason.decode!/1)

      assert [%{"name" => "A"}, %{"name" => "B"}] = decoded
    end

    test "ignores non-map entries" do
      assert [_, _] = JsonLd.entries(%{json_ld: ["bogus", 42, nil]})
    end
  end

  describe "for_home/1" do
    test "describes the Cure language as a SoftwareApplication" do
      schema = JsonLd.for_home("9.9.9")

      assert schema["@type"] == "SoftwareApplication"
      assert schema["softwareVersion"] == "9.9.9"
      assert schema["programmingLanguage"] == "Cure"
      assert schema["operatingSystem"] =~ "BEAM"
      assert schema["codeRepository"] == "https://github.com/cure-lang/cure-lang"
      assert schema["offers"]["price"] == "0"
    end
  end

  describe "for_page/1" do
    test "infers HowTo for getting-started and lifts <h2>s into HowToSteps" do
      page = Pages.get_page_by_id!("getting-started")
      schema = JsonLd.for_page(page)

      assert schema["@type"] == "HowTo"
      assert schema["name"] == page.title
      assert is_list(schema["step"])
      # `getting-started.md` has at least three H2 sections; lifting
      # them into HowToSteps is the whole point of the inference.
      assert match?([_, _, _ | _], schema["step"])
      assert Enum.all?(schema["step"], &(&1["@type"] == "HowToStep"))
      assert Enum.all?(schema["step"], &is_integer(&1["position"]))
    end

    test "defaults to TechArticle for ordinary documentation pages" do
      page = Pages.get_page_by_id!("language-guide")
      schema = JsonLd.for_page(page)

      assert schema["@type"] == "TechArticle"
      assert schema["name"] == page.title
      assert schema["description"] == page.description
      assert String.ends_with?(schema["url"], "/language-guide")
    end

    test "infers FAQPage when the body contains enough Q-style headings" do
      page = %Pages.Page{
        id: "faq",
        title: "FAQ",
        description: "FAQ",
        order: 1,
        body: """
        <h2>What is Cure?</h2><p>...</p>
        <h2>Why dependent types?</h2><p>...</p>
        <h2>How do I install it?</h2><p>...</p>
        """
      }

      schema = JsonLd.for_page(page)

      assert schema["@type"] == "FAQPage"
      assert match?([_, _, _], schema["mainEntity"])
      assert Enum.all?(schema["mainEntity"], &(&1["@type"] == "Question"))
    end
  end

  describe "for_blog_index/1 and for_blog_post/1" do
    test "blog index is a Blog with one BlogPosting per post" do
      posts = Blog.all_posts()
      schema = JsonLd.for_blog_index(posts)

      assert schema["@type"] == "Blog"
      assert length(schema["blogPost"]) == length(posts)
      assert Enum.all?(schema["blogPost"], &(&1["@type"] == "BlogPosting"))
    end

    test "individual blog post is a TechArticle with author and tags" do
      post = Blog.all_posts() |> List.first()
      schema = JsonLd.for_blog_post(post)

      assert schema["@type"] == "TechArticle"
      assert schema["headline"] == post.title
      assert schema["author"]["name"] == post.author
      assert schema["datePublished"] == Date.to_iso8601(post.date)
      assert schema["keywords"] == Enum.join(post.tags, ", ")
    end
  end

  describe "for_stdlib_index/1 and for_stdlib_module/1" do
    test "stdlib index is a CollectionPage carrying an ItemList" do
      modules = Stdlib.modules()
      schema = JsonLd.for_stdlib_index(modules)

      assert schema["@type"] == "CollectionPage"
      assert schema["mainEntity"]["@type"] == "ItemList"
      assert schema["mainEntity"]["numberOfItems"] == length(modules)
      assert Enum.all?(schema["mainEntity"]["itemListElement"], &(&1["@type"] == "ListItem"))
    end

    test "individual stdlib module is an APIReference with programmingLanguage = Cure" do
      mod = Stdlib.modules() |> List.first()
      schema = JsonLd.for_stdlib_module(mod)

      assert schema["@type"] == "APIReference"
      assert schema["name"] == mod.module
      assert schema["programmingLanguage"] == "Cure"
      assert schema["targetPlatform"] =~ "BEAM"
      assert is_binary(schema["description"]) and schema["description"] != ""
    end
  end

  describe "for_playground/0 and for_repl/0" do
    test "playground and REPL surfaces are WebApplications" do
      assert JsonLd.for_playground()["@type"] == "WebApplication"
      assert JsonLd.for_repl()["@type"] == "WebApplication"
    end
  end

  describe "for_error/1" do
    test "produces a WebPage tagged with the HTTP status" do
      schema = JsonLd.for_error(404)
      assert schema["@type"] == "WebPage"
      assert schema["name"] =~ "404"
      assert schema["url"] =~ "/errors/404"
    end
  end

  describe "GET / (rendered HTML)" do
    test "embeds at least three JSON-LD blocks (baseline + page-specific)", %{conn: conn} do
      body =
        conn
        |> get(~p"/")
        |> html_response(200)

      blocks =
        ~r{<script type="application/ld\+json">\s*(.+?)\s*</script>}s
        |> Regex.scan(body, capture: :all_but_first)
        |> List.flatten()
        |> Enum.map(&Jason.decode!/1)

      assert match?([_, _, _ | _], blocks),
             "expected baseline (WebSite + Organization) plus a page-specific schema"

      types = Enum.map(blocks, & &1["@type"])
      assert "WebSite" in types
      assert "Organization" in types
      assert "SoftwareApplication" in types
    end

    test "blog post page emits a TechArticle schema", %{conn: conn} do
      post = Blog.all_posts() |> List.first()

      body =
        conn
        |> get(~p"/blog/#{post.id}")
        |> html_response(200)

      types =
        ~r{<script type="application/ld\+json">\s*(.+?)\s*</script>}s
        |> Regex.scan(body, capture: :all_but_first)
        |> List.flatten()
        |> Enum.map(&Jason.decode!/1)
        |> Enum.map(& &1["@type"])

      assert "TechArticle" in types
    end

    test "stdlib module page emits an APIReference schema", %{conn: conn} do
      mod = Stdlib.modules() |> List.first()

      body =
        conn
        |> get(~p"/stdlib/#{mod.module}")
        |> html_response(200)

      types =
        ~r{<script type="application/ld\+json">\s*(.+?)\s*</script>}s
        |> Regex.scan(body, capture: :all_but_first)
        |> List.flatten()
        |> Enum.map(&Jason.decode!/1)
        |> Enum.map(& &1["@type"])

      assert "APIReference" in types
    end
  end

  # ---------------------------------------------------------------------------

  # `WebSite` references its publisher by `@id`, which is the
  # Organization's `@id`. The two `@id`s share a base URL but differ
  # in their fragment, so derive the org ID from the website ID.
  defp ref_to_org(website_id) do
    String.replace(website_id, "#website", "#organization")
  end
end
