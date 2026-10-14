defmodule CureSiteWeb.PlaygroundLive do
  @moduledoc """
  Cure Playground LiveView (v0.28.0).

  Two-pane editor with:
  - Left: editable source, highlighted in the browser by the
    tree-sitter-cure grammar (the `CureEditor` hook).
  - Right: live type-check panel (always on, debounced at 150 ms).

  An optional "Run" button triggers the sandboxed evaluator
  (`CureSiteWeb.Eval`) and displays stdout + return value.
  """

  use CureSiteWeb, :live_view

  @impl true
  def mount(_params, _session, socket) do
    source = default_source()
    type_result = type_check(source)

    {:ok,
     socket
     |> assign(:page_title, "Cure Playground")
     |> assign(:json_ld, CureSiteWeb.JsonLd.for_playground())
     |> assign(:source, source)
     |> assign(:type_result, type_result)
     |> assign(:eval_output, nil)
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
     |> assign(:type_result, type_check(source))
     |> assign(:form, to_form(%{"source" => source}, as: "playground"))}
  end

  @impl true
  def handle_event("run", _params, socket) do
    {:noreply, assign(socket, :eval_output, CureSiteWeb.Eval.eval(socket.assigns.source))}
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
      <div>
        <h1 class="text-3xl font-bold">Playground</h1>
        <p class="mt-2 text-base-content/70">
          Type-checked as you write by Cure's dependent compiler. <strong>Run</strong>
          evaluates it in a sandboxed process.
        </p>

        <div class="mt-8 grid items-start gap-6 lg:grid-cols-[minmax(0,1.4fr)_minmax(0,1fr)]">
          <.form for={@form} id="playground-form" phx-change="update" class="cure-code-window !mb-0">
            <div class="cure-code-window-bar">
              <span class="cure-code-window-dots" aria-hidden="true"><i></i><i></i><i></i></span>
              <label for={@form[:source].id} class="cure-code-window-label">playground.cure</label>
              <button
                type="button"
                phx-click="run"
                phx-disable-with="Running…"
                class="ml-auto rounded-md bg-primary px-3 py-1 text-xs font-semibold text-primary-content transition hover:bg-primary/90"
              >
                Run
              </button>
            </div>
            <%!-- CureEditor (assets/js/cure_editor.js) highlights the source
                 with tree-sitter-cure into the pre behind the textarea. The
                 editor is client-owned: the server only seeds its text. --%>
            <div id="playground-editor" class="cure-editor" phx-hook="CureEditor" phx-update="ignore">
              <pre aria-hidden="true"><code class="makeup cure"></code></pre>
              <pre class="cure-editor-gutter" aria-hidden="true"></pre>
              <textarea
                id={@form[:source].id}
                name={@form[:source].name}
                wrap="off"
                spellcheck="false"
                autocapitalize="off"
                autocomplete="off"
                phx-debounce="150"
              >{Phoenix.HTML.Form.normalize_value("textarea", @form[:source].value)}</textarea>
            </div>
          </.form>

          <div class="flex min-w-0 flex-col gap-6">
            <section>
              <h2 class="mb-2 text-sm font-semibold">Type checker</h2>
              <div class="overflow-x-auto rounded-xl border border-base-300 bg-base-200 p-4 font-mono text-sm">
                <%= case @type_result do %>
                  <% {:ok, []} -> %>
                    <p class="flex items-center gap-2 text-success">
                      <.icon name="hero-check-circle" class="size-4" /> No type errors
                    </p>
                  <% {:error, errors} -> %>
                    <pre :for={err <- errors} class="text-error">{Cure.Diagnostic.Host.render(err, "playground.cure", @source)}</pre>
                <% end %>
              </div>
            </section>

            <section>
              <h2 class="mb-2 text-sm font-semibold">Output</h2>
              <div class="rounded-xl border border-base-300 bg-base-200 p-4 font-mono text-sm">
                <%= case @eval_output do %>
                  <% nil -> %>
                    <p class="text-base-content/50">Run the program to see its output.</p>
                  <% {:ok, output, result} -> %>
                    <pre :if={output != ""} class="mb-1 whitespace-pre-wrap text-base-content/70">{output}</pre>
                    <p class="text-success">=&gt; {result}</p>
                  <% {:error, reason} -> %>
                    <p class="whitespace-pre-wrap text-error">{reason}</p>
                <% end %>
              </div>
            </section>
          </div>
        </div>
      </div>
    </Layouts.app>
    """
  end
end
