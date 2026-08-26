defmodule CureSiteWeb.StdlibHTML do
  @moduledoc """
  HEEx templates for `CureSiteWeb.StdlibController`. Embeds every file
  under `stdlib_html/` (index, show, and the shared sidebar partial).
  """

  use CureSiteWeb, :html

  alias CureSite.Stdlib

  embed_templates("stdlib_html/*")

  @doc "Render a module's public function signature as inline HTML."
  def render_signature(f) do
    params =
      f.params
      |> Enum.map_join(", ", fn {name, type} ->
        ~s|#{escape(name)}: <span class="text-emerald-600 dark:text-emerald-400">#{escape(type)}</span>|
      end)

    ret =
      if f.return_type,
        do:
          ~s| -&gt; <span class="text-emerald-600 dark:text-emerald-400">#{escape(f.return_type)}</span>|,
        else: ""

    effects =
      case f.effects do
        [] -> ""
        effs -> ~s| <span class="text-rose-500">! #{escape(Enum.join(effs, ", "))}</span>|
      end

    html =
      ~s|<span class="text-primary font-semibold">#{escape(f.name)}</span>| <>
        "(" <> params <> ")" <> ret <> effects

    Phoenix.HTML.raw(html)
  end

  defp escape(s) when is_binary(s),
    do: s |> Phoenix.HTML.html_escape() |> Phoenix.HTML.safe_to_string()

  defp escape(other), do: escape(to_string(other))

  @doc "Render a module doc body (markdown -> HTML)."
  def render_doc(nil), do: Phoenix.HTML.raw("")
  def render_doc(""), do: Phoenix.HTML.raw("")
  def render_doc(md), do: Phoenix.HTML.raw(Stdlib.markdown_to_html(md))

  @doc "Public function entries for a module (sorted, private functions dropped)."
  def public_functions(module) do
    (module.functions || [])
    |> Enum.filter(&(&1.visibility == :public))
    |> Enum.sort_by(&{&1.name, length(&1.params)})
  end

  @doc "Short first-paragraph preview for use in the stdlib index cards."
  def first_line(nil), do: ""
  def first_line(""), do: ""

  def first_line(body) when is_binary(body) do
    body
    |> String.split(~r/\n\s*\n/, parts: 2)
    |> List.first()
    |> to_string()
    |> String.trim()
  end

  @doc "Textual suffix for a type declaration (variants or refinement marker)."
  def variants_suffix(%{variants: v}) when is_list(v) and v != [],
    do: " = " <> Enum.join(v, " | ")

  def variants_suffix(%{refinement: true}), do: " (refinement)"
  def variants_suffix(_), do: ""

  @doc "Textual suffix for a protocol declaration (its type parameters)."
  def proto_params_suffix(%{type_params: [_ | _] = params}),
    do: "(" <> Enum.join(params, ", ") <> ")"

  def proto_params_suffix(_), do: ""
end
