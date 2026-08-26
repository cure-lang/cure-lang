defmodule CureSite.Stdlib do
  @moduledoc """
  Compile-time bundle of the Cure standard library, extracted from the
  actual `.cure` sources shipped in `cure/lib/std/` and turned into
  `MDEx`-rendered HTML (via `CureSite.MarkdownConverter`) ready for
  `stdlib_html/*.heex` to splice in.

  Walking the filesystem at compile time means two things:

    * the site ships identical copy to what `cure doc` produces from
      the same sources, so they cannot drift;
    * a fresh `mix phx.server` has zero I/O cost -- every doc map is a
      module attribute in the finished beam.

  Host integration:

    * `modules/0`  -> list of module doc maps, sorted by name
    * `module/1`   -> fetch a single module doc map (or `nil`)
    * `groups/0`   -> ordered `[{group_name, [module_doc_map, ...]}]`
      list produced by applying `@groups_for_modules` to the extracted
      bundle. Modules that do not appear in any group fall into the
      trailing "Other" bucket.
    * `source_url/2` -> GitHub URL for a module (and optional symbol).
  """

  alias Cure.Doc.Extractor

  @source_base "https://github.com/cure-lang/cure-lang/blob/main/lib/std/"

  # Curated grouping used by the `/stdlib` pages. The order here is the
  # order the sidebar renders. Stdlib modules added in future releases
  # that are not listed below fall into the trailing "Other" bucket so
  # nothing gets silently dropped.
  @groups_for_modules [
    {"Core", ["Std.Core", "Std.Equal", "Std.Eq", "Std.Ord", "Std.Show", "Std.Functor"]},
    {"Collections",
     [
       "Std.List",
       "Std.Map",
       "Std.Set",
       "Std.Pair",
       "Std.Vector",
       "Std.Iter",
       "Std.Access",
       "Std.Match"
     ]},
    {"Text & Regex", ["Std.String", "Std.Regex"]},
    {"Numeric", ["Std.Math"]},
    {"I/O & System", ["Std.Io", "Std.System", "Std.Time"]},
    {"Concurrency",
     ["Std.Actor", "Std.Process", "Std.Supervisor", "Std.Fsm", "Std.App", "Std.CRDT"]},
    {"Error & Option", ["Std.Option", "Std.Result"]},
    {"Testing & Proofs", ["Std.Test", "Std.Gen", "Std.Proof"]},
    {"Network", ["Std.Http", "Std.Json"]}
  ]

  # Discover the stdlib source tree at compile time. The site is built
  # inside the Cure repository, so `lib/std/` sits two directories up
  # from `cure/site/lib/cure_site/`. Using `Path.expand/2` keeps the
  # lookup robust in the face of future layout tweaks.
  @stdlib_dir Path.expand("../../../lib/std", __DIR__)

  @cure_files (if File.dir?(@stdlib_dir) do
                 @stdlib_dir
                 |> Path.join("*.cure")
                 |> Path.wildcard()
                 |> Enum.sort()
               else
                 []
               end)

  for file <- @cure_files, do: @external_resource(file)

  # `Cure.Compiler.Lexer.tokenize/2` emits `:token_produced` events
  # through the `Cure.Pipeline.Events.Registry`. That Registry is part
  # of `Cure.Application`'s supervision tree and is therefore not
  # running at compile time unless we poke `:cure` awake first.
  _ = Application.ensure_all_started(:cure)

  @modules (for file <- @cure_files,
                {:ok, tokens} <-
                  [Cure.Compiler.Lexer.tokenize(File.read!(file), file: file, emit_events: false)],
                {:ok, ast} <-
                  [Cure.Compiler.Parser.parse(tokens, file: file, emit_events: false)],
                %{module: mod} = doc <- [Extractor.extract(ast)],
                is_binary(mod),
                mod != "Unknown",
                String.starts_with?(mod, "Std.") do
              Map.put(doc, :__source_file, Path.basename(file))
            end)
           |> Enum.sort_by(& &1.module)

  @doc "Return every extracted Std.* module, sorted by name."
  @spec modules() :: [map()]
  def modules, do: @modules

  @doc "Fetch a single module doc map (or `nil` when missing)."
  @spec module(String.t()) :: map() | nil
  def module(name) when is_binary(name) do
    Enum.find(@modules, &(&1.module == name))
  end

  @doc """
  Return the curated grouping used by `/stdlib`. The shape is
  `[{group_name, [module_doc_map, ...]}]`. Modules that do not appear
  in any configured group land in a trailing `"Other"` bucket.
  """
  @spec groups() :: [{String.t(), [map()]}]
  def groups do
    by_name = Map.new(@modules, &{&1.module, &1})

    curated =
      @groups_for_modules
      |> Enum.map(fn {name, mods} ->
        {name, Enum.flat_map(mods, fn m -> List.wrap(Map.get(by_name, m)) end)}
      end)
      |> Enum.reject(fn {_, xs} -> xs == [] end)

    declared = Enum.flat_map(@groups_for_modules, fn {_, xs} -> xs end)
    leftover = Enum.reject(@modules, &(&1.module in declared))

    if leftover == [], do: curated, else: curated ++ [{"Other", leftover}]
  end

  @doc """
  Return the GitHub source URL for a module (optionally focussed on a
  symbol anchor). The URL is stable because it points to the file in
  `lib/std/` on `main`.
  """
  @spec source_url(map() | String.t(), String.t() | nil) :: String.t()
  def source_url(module, symbol \\ nil)

  def source_url(%{__source_file: file}, symbol), do: build_source_url(file, symbol)

  def source_url(name, symbol) when is_binary(name) do
    case module(name) do
      %{__source_file: file} -> build_source_url(file, symbol)
      _ -> @source_base
    end
  end

  defp build_source_url(file, nil), do: @source_base <> file

  defp build_source_url(file, symbol),
    do: @source_base <> file <> "#" <> URI.encode_www_form(symbol)

  @doc """
  Render the supplied markdown to HTML using the same converter the
  rest of the site uses. Accepts `nil` so templates can blindly render
  missing docstrings.

  Delegates to `CureSite.MarkdownConverter.to_html/1`, which is
  runtime-safe: it routes through `MDEx` (a direct runtime dependency)
  and `Makeup.Registry` instead of `Earmark` or `NimblePublisher`,
  both of which were only available transitively through
  `:nimble_publisher` and therefore missing from the production
  release.
  """
  @spec markdown_to_html(String.t() | nil) :: String.t()
  defdelegate markdown_to_html(body), to: CureSite.MarkdownConverter, as: :to_html
end
