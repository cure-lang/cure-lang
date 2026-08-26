defmodule CureSite.PagesTest do
  use ExUnit.Case, async: true

  alias CureSite.Pages
  alias CureSite.Pages.TechnicalOverview

  describe "the About page" do
    test "is rendered from the repository's technical overview" do
      path = TechnicalOverview.source_path()

      assert String.ends_with?(path, "docs/TECHNICAL_OVERVIEW.md")
      assert File.exists?(path), "expected #{path} to exist"
    end

    test "is served as /about with its own category" do
      page = Pages.get_page_by_id!("about")

      assert page.id == "about"
      assert page.title == "Technical Overview"
      assert page.category == :about
      assert page.category_title == "About"
      assert page.order > 0
      assert page.description =~ "compiler"
    end

    test "carries the document body, rendered to HTML, without a duplicate title" do
      page = Pages.get_page_by_id!("about")

      # Section headings of `docs/TECHNICAL_OVERVIEW.md`, so the body is
      # genuinely the repository document rather than a placeholder.
      assert page.body =~ "Design Philosophy"
      assert page.body =~ "The Compiler Pipeline"
      assert page.body =~ "The Dependent Type System"

      # The document's own `# ...` heading is dropped: the page layout
      # renders `page.title` as the single `<h1>`.
      refute page.body =~ "<h1"
    end

    test "is enumerated with every other page" do
      ids = Enum.map(Pages.all_pages(), & &1.id)

      assert "about" in ids
      assert "getting-started" in ids
    end

    test "leads the docs sidebar and the prev/next chain" do
      assert [{:about, "About", _desc, about_pages} | _rest] = Pages.grouped_pages()
      assert [%{id: "about"}] = about_pages

      assert {nil, next} = Pages.prev_and_next("about")
      assert next.id == "getting-started"
    end
  end
end
