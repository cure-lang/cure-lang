defmodule Mix.Tasks.Katex.Fonts do
  @shortdoc "Stages the KaTeX web fonts next to the generated app.css"

  @moduledoc """
  Copies the KaTeX web fonts into `priv/static/assets/css/fonts`.

  `assets/css/app.css` imports `katex.min.css` out of
  `assets/node_modules`. That stylesheet declares its `@font-face`
  sources relatively:

      src: url(fonts/KaTeX_Main-Regular.woff2) format("woff2"), ...

  Tailwind v4 inlines `@import`-ed stylesheets but does **not** rewrite
  `url()` references, and the bundle is written to
  `priv/static/assets/css/app.css`. The browser therefore resolves those
  sources against `/assets/css/`, which is why the fonts have to live in
  `priv/static/assets/css/fonts`. Without them KaTeX silently degrades
  to the browser's default serif face and the typesetting metrics -- the
  whole point of KaTeX -- fall apart.

  The task is wired into the `assets.setup`, `assets.build` and
  `assets.deploy` aliases in `mix.exs`, and runs before `phx.digest` so
  the fonts get digested and their URLs rewritten along with everything
  else under `priv/static`.

  Files are compared by size and mtime, so repeated runs are cheap and
  do not needlessly invalidate the live-reload watcher.
  """

  use Mix.Task

  @source_dir Path.join(~w[assets node_modules katex dist fonts])
  @target_dir Path.join(~w[priv static assets css fonts])

  @impl Mix.Task
  def run(_args) do
    root = Path.dirname(Mix.Project.project_file())
    source = Path.join(root, @source_dir)
    target = Path.join(root, @target_dir)

    if not File.dir?(source) do
      Mix.raise("""
      KaTeX fonts not found at #{Path.relative_to_cwd(source)}.

      Install the JavaScript dependencies first:

          mix assets.setup
      """)
    end

    File.mkdir_p!(target)

    copied =
      source
      |> File.ls!()
      |> Enum.sort()
      |> Enum.count(&copy_if_stale(Path.join(source, &1), Path.join(target, &1)))

    Mix.shell().info([
      :green,
      "* katex.fonts ",
      :reset,
      "#{copied} font(s) copied to #{Path.relative_to_cwd(target)}"
    ])

    :ok
  end

  # Returns `true` when the file was (re)copied, `false` when the target
  # was already up to date.
  defp copy_if_stale(source, target) do
    if stale?(source, target) do
      File.cp!(source, target)
      true
    else
      false
    end
  end

  defp stale?(source, target) do
    case {File.stat(source), File.stat(target)} do
      {{:ok, %File.Stat{size: size, mtime: source_mtime}},
       {:ok, %File.Stat{size: size, mtime: target_mtime}}} ->
        source_mtime > target_mtime

      _otherwise ->
        true
    end
  end
end
