defmodule CureSiteWeb.PlaygroundLive do
  @moduledoc """
  Cure Playground LiveView (v0.28.0).

  Two-pane editor with:
  - Left: editable source with live syntax highlighting.
  - Right: live type-check panel (always on, debounced at 150 ms).

  An optional "Run" button triggers the sandboxed evaluator
  (`CureSiteWeb.Eval`) and displays stdout + return value.
  """

  use CureSiteWeb, :live_view

  alias Makeup.Registry

  @impl true
  def mount(_params, _session, socket) do
    source = default_source()
    highlighted = highlight(source)
    type_result = type_check(source)

    {:ok,
     socket
     |> assign(:page_title, "Cure Playground")
     |> assign(:json_ld, CureSiteWeb.JsonLd.for_playground())
     |> assign(:source, source)
     |> assign(:highlighted, highlighted)
     |> assign(:type_result, type_result)
     |> assign(:eval_output, nil)
     |> assign(:eval_running, false)
     |> assign(:form, to_form(%{"source" => source}, as: "playground"))}
  end

  @impl true
  def handle_event(
        "update",
        %{"playground" => %{"source" => source}},
        socket
      ) do
    {:noreply,
     socket
     |> assign(:source, source)
     |> assign(:highlighted, highlight(source))
     |> assign(:type_result, type_check(source))
     |> assign(:form, to_form(%{"source" => source}, as: "playground"))}
  end

  @impl true
  def handle_event("run", _params, socket) do
    socket = assign(socket, :eval_running, true)

    case CureSiteWeb.Eval.eval(socket.assigns.source) do
      {:ok, output, result} ->
        {:noreply,
         socket
         |> assign(:eval_output, {:ok, output, result})
         |> assign(:eval_running, false)}

      {:error, reason} ->
        {:noreply,
         socket
         |> assign(:eval_output, {:error, reason})
         |> assign(:eval_running, false)}
    end
  end

  # -- Internals ---------------------------------------------------------------

  defp default_source do
    """
    mod Demo
      fn add(a: Int, b: Int) -> Int = a + b

      fn doubled(xs: List(Int)) -> List(Int) =
        xs |> Std.List.map(fn (x) -> x * 2)

      fn main() -> Int = add(1, 2)
    """
  end

  defp highlight(source) when is_binary(source) do
    case Registry.fetch_lexer_by_name("cure") do
      {:ok, {lexer, opts}} ->
        source
        |> lexer.lex(opts)
        |> Makeup.Formatters.HTML.HTMLFormatter.format_as_iolist([])
        |> IO.iodata_to_binary()

      :error ->
        Phoenix.HTML.html_escape(source) |> Phoenix.HTML.safe_to_string()
    end
  rescue
    _ ->
      Phoenix.HTML.html_escape(source) |> Phoenix.HTML.safe_to_string()
  end

  # Run the same dependent compiler pipeline used by builds, stopping at a
  # scratch BEAM artifact rather than loading submitted code into the site VM.
  # The panel keeps its historical `{:error, [reason]}` shape for rendering.
  defp type_check(source) when is_binary(source) do
    case Cure.Compiler.compile_string(source,
           file: "playground.cure",
           output_dir: Path.join(System.tmp_dir!(), "cure_site_playground_check"),
           emit_events: false
         ) do
      {:ok, _module, _warnings} -> {:ok, []}
      {:error, reason} -> {:error, [reason]}
    end
  rescue
    _ -> {:ok, []}
  end

  @impl true
  def render(assigns) do
    ~H"""
    <Layouts.app flash={@flash}>
      <main class="mx-auto max-w-6xl p-6">
        <h1 class="text-3xl font-bold mb-2">Cure Playground</h1>
        <p class="text-gray-500 text-sm mb-6">
          Live type-checking powered by Cure's dependent compiler.
          Hit <strong>Run</strong> to evaluate in a sandboxed process.
        </p>

        <div class="grid grid-cols-1 lg:grid-cols-2 gap-6">
          <%!-- Left: editor + run button --%>
          <div class="flex flex-col gap-3">
            <.form
              for={@form}
              id="playground-form"
              phx-change="update"
              class="flex flex-col gap-2"
            >
              <label class="block text-sm font-semibold">Source</label>
              <.input
                field={@form[:source]}
                type="textarea"
                rows="24"
                class="w-full font-mono text-sm border rounded p-3"
                phx-debounce="150"
              />
            </.form>

            <button
              phx-click="run"
              disabled={@eval_running}
              class="self-start px-4 py-2 bg-indigo-600 text-white rounded text-sm font-medium hover:bg-indigo-700 disabled:opacity-50 disabled:cursor-not-allowed transition-colors"
            >
              {if @eval_running, do: "Running...", else: "Run"}
            </button>

            <%= if @eval_output do %>
              <div class="border rounded p-3 bg-gray-50 font-mono text-sm">
                <%= case @eval_output do %>
                  <% {:ok, output, result} -> %>
                    <%= if output != "" do %>
                      <p class="text-gray-600 mb-1 whitespace-pre">{output}</p>
                    <% end %>
                    <p class="text-green-700">=&gt; {result}</p>
                  <% {:error, reason} -> %>
                    <p class="text-red-700 whitespace-pre-wrap">{reason}</p>
                <% end %>
              </div>
            <% end %>
          </div>

          <%!-- Right: type-check panel + highlighted preview --%>
          <div class="flex flex-col gap-3">
            <div>
              <label class="block text-sm font-semibold mb-2">Type Checker</label>
              <div class="border rounded p-3 min-h-16 font-mono text-sm bg-gray-50">
                <%= case @type_result do %>
                  <% {:ok, []} -> %>
                    <span class="text-green-700 font-semibold">OK -- no type errors</span>
                  <% {:error, errors} -> %>
                    <%= for err <- errors do %>
                      <p class="text-red-700 mb-1">
                        {Cure.Diagnostic.Host.render(err, "playground.cure", @source)}
                      </p>
                    <% end %>
                <% end %>
              </div>
            </div>

            <div>
              <label class="block text-sm font-semibold mb-2">Highlighted</label>
              <pre class="border rounded p-3 overflow-auto font-mono text-sm bg-gray-900 text-gray-100 min-h-64"><code class="makeup cure">{Phoenix.HTML.raw(@highlighted)}</code></pre>
            </div>
          </div>
        </div>
      </main>
    </Layouts.app>
    """
  end
end
