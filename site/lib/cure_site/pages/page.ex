defmodule CureSite.Pages.Page do
  @enforce_keys [:id, :title, :body, :description, :order]
  defstruct [:id, :title, :body, :description, :order, category: :learn, category_title: "Learn Cure"]

  def build(filename, attrs, body) do
    id = filename |> Path.rootname() |> Path.split() |> List.last()
    attrs = Map.merge(%{category: :learn, category_title: "Learn Cure"}, attrs)
    struct!(__MODULE__, [id: id, body: body] ++ Map.to_list(attrs))
  end
end
