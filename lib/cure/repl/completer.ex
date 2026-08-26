defmodule Cure.REPL.Completer do
  @moduledoc """
  Prefix-based tab-completion for the REPL.

  `complete/2` inspects the buffer + cursor and returns:

    * `{:unique, text}` -- a single candidate; caller replaces prefix.
    * `{:partial, common, candidates}` -- longest common prefix plus
      the list of candidates to offer the user on a second Tab.
    * `:none` -- nothing to offer.

  The priority order is meta-command names, then meta-command
  arguments (file paths for `:load`/`:save`/`:edit`, modules for
  `:use`/`:doc`), then Cure keywords as a fallback.
  """

  @meta_commands ~w(
    :t :type :doc :effects :load :reload :use :holes :env :reset :fmt
    :help :h :quit :q :exit :history :clear :save :edit :time :bench
    :ast :theme :mode :color :search
  )

  @keywords ~w(
    fn mod rec actor fsm sup app interface implementation type typealias
    primitive deriving local use let in for pickup else match with when
    proof have because rewrite simplify induction case return throw try catch
    finally spawn send receive after unsafe quote true false nil and or not
    Int Float String Bool Atom List Tuple Map Set
  )

  @theme_names ~w(dark light mono)
  @mode_names ~w(emacs vi)
  @color_names ~w(on off)

  @doc "Compute a completion for the given buffer + cursor position."
  @spec complete(String.t(), non_neg_integer()) ::
          {:unique, String.t()}
          | {:partial, String.t(), [String.t()]}
          | :none
  def complete(buffer, cursor) do
    {prefix, token} = split_prefix(buffer, cursor)

    candidates = candidates_for(prefix, token)

    case candidates do
      [] ->
        :none

      [single] ->
        {:unique, finish(prefix, single, token)}

      many ->
        common = longest_common_prefix(many)

        if common == token or common == "" do
          {:partial, common, many}
        else
          {:unique, finish(prefix, common, token)}
        end
    end
  end

  defp candidates_for(prefix, token) do
    cond do
      # We haven't typed anything yet.
      prefix == "" and token == "" ->
        []

      # Meta-command in progress (leading `:`)
      prefix == "" and String.starts_with?(token, ":") ->
        Enum.filter(@meta_commands, &String.starts_with?(&1, token))

      # File path arguments for :load / :save / :edit
      meta_arg?(prefix) == :path ->
        path_candidates(token)

      # Module name for :use / :doc
      meta_arg?(prefix) == :module ->
        module_candidates(token)

      # Named theme
      meta_arg?(prefix) == :theme ->
        Enum.filter(@theme_names, &String.starts_with?(&1, token))

      meta_arg?(prefix) == :mode ->
        Enum.filter(@mode_names, &String.starts_with?(&1, token))

      meta_arg?(prefix) == :color ->
        Enum.filter(@color_names, &String.starts_with?(&1, token))

      # Cure keyword fallback.
      token != "" ->
        Enum.filter(@keywords, &String.starts_with?(&1, token))

      true ->
        []
    end
  end

  @doc false
  def meta_arg?(prefix) do
    trimmed = String.trim_leading(prefix)

    cond do
      trimmed == "" ->
        :none

      Regex.match?(~r/^:(load|save|edit)\s+$/, trimmed) ->
        :path

      Regex.match?(~r/^:(use|doc)\s+$/, trimmed) ->
        :module

      Regex.match?(~r/^:theme\s+$/, trimmed) ->
        :theme

      Regex.match?(~r/^:mode\s+$/, trimmed) ->
        :mode

      Regex.match?(~r/^:color\s+$/, trimmed) ->
        :color

      true ->
        :none
    end
  end

  defp split_prefix(buffer, cursor) do
    left = String.slice(buffer, 0, cursor)

    case Regex.run(~r/^(.*?)([\w:.\/~-]*)$/u, left, capture: :all_but_first) do
      [prefix, token] -> {prefix, token}
      _ -> {left, ""}
    end
  end

  defp finish(prefix, completion, _token), do: prefix <> completion

  defp longest_common_prefix([single]), do: single

  defp longest_common_prefix([first | rest]) do
    Enum.reduce(rest, first, &common/2)
  end

  defp common(a, b), do: common(a, b, "")

  defp common(<<c, arest::binary>>, <<c, brest::binary>>, acc),
    do: common(arest, brest, acc <> <<c>>)

  defp common(_, _, acc), do: acc

  # The old implementation returned bare basenames, which is fine when
  # the user's token has no path separators (e.g. `:load exa` completes
  # to `:load examples/`), but broke every nested lookup: typing
  # `:load examples/let` and hitting Tab silently dropped the
  # `examples/` prefix and produced `:load let_destructuring.cure`,
  # which is neither what the user wrote nor a valid path.
  #
  # The fix is to echo back the same visible directory prefix the user
  # typed (`./`, `examples/`, `~/src/`, `/opt/...`, or nothing for a
  # bare name in `.`) so the candidate, and therefore the longest common
  # prefix used to replace the token, always rebuilds the full path.
  defp path_candidates(token) do
    {user_dir, dir, pattern} =
      cond do
        token == "" ->
          {"", ".", "*"}

        String.ends_with?(token, "/") ->
          {token, Path.expand(token), "*"}

        true ->
          {dirname_display(token), Path.expand(Path.dirname(token)), Path.basename(token) <> "*"}
      end

    case File.ls(dir) do
      {:ok, entries} ->
        entries
        |> Enum.filter(&glob_match?(&1, pattern))
        |> Enum.map(fn entry ->
          full = Path.join(dir, entry)
          name = if File.dir?(full), do: entry <> "/", else: entry
          user_dir <> name
        end)
        |> Enum.sort()

      _ ->
        []
    end
  end

  # Reconstruct the user-visible directory prefix of `token`:
  #
  #   - `"ex"`              -> `""`       (bare name in cwd)
  #   - `"./ex"`            -> `"./"`     (explicit cwd-relative)
  #   - `"examples/let"`    -> `"examples/"`
  #   - `"~/src/foo"`       -> `"~/src/"`
  #   - `"/tmp/foo"`        -> `"/tmp/"`
  #   - `"/foo"`            -> `"/"`
  defp dirname_display(token) do
    case Path.dirname(token) do
      "." -> if String.contains?(token, "/"), do: "./", else: ""
      "/" -> "/"
      other -> other <> "/"
    end
  end

  defp glob_match?(entry, pattern) do
    regex =
      pattern
      |> Regex.escape()
      |> String.replace("\\*", ".*")
      |> then(&("^" <> &1 <> "$"))
      |> Regex.compile!()

    Regex.match?(regex, entry)
  end

  defp module_candidates(token) do
    # Walk every module currently loaded in the VM, filtering to ones
    # that look like they came from Cure stdlib / user modules (start
    # with an uppercase letter, no dot prefix).
    :code.all_loaded()
    |> Enum.map(fn {mod, _} -> Atom.to_string(mod) end)
    |> Enum.filter(&cure_module?/1)
    |> Enum.filter(&String.starts_with?(&1, token))
    |> Enum.sort()
    |> Enum.uniq()
  end

  defp cure_module?(name) do
    String.match?(name, ~r/^[A-Z][A-Za-z0-9]+(\.[A-Z][A-Za-z0-9]+)*$/) and
      not String.starts_with?(name, ["Cure.", "Elixir.", "IEx.", "Mix."])
  end

  @doc false
  def __keywords__, do: @keywords

  @doc false
  def __meta_commands__, do: @meta_commands
end
