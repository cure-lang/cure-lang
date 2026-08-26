defmodule Cure.Migrate.LegacyOtp do
  @moduledoc """
  Reader-side normalisation for the transparent OTP surface that predates the
  structured `actor`/`fsm`/`sup`/`app` families.

  These forms cannot reach the AST migration rules: the current parser quite
  correctly rejects them before a rule can run.  This small, line-oriented
  bridge is therefore deliberately limited to the unambiguous legacy headers
  used by the checked-in examples.  It only changes declaration framing; the
  callback expressions and comments remain source text for the ordinary parser
  and subsequent AST rules.
  """

  @doc "Return `{normalised_source, changed?}` for legacy transparent OTP forms."
  @spec normalize(String.t()) :: {String.t(), boolean()}
  def normalize(source) when is_binary(source) do
    lines = String.split(source, "\n", trim: false)
    {out, changed?} = normalize_lines(lines, [], false)
    {Enum.join(out, "\n"), changed?}
  end

  defp normalize_lines([], acc, changed), do: {Enum.reverse(acc), changed}

  defp normalize_lines([line | rest], acc, changed) do
    case normalize_header(line) do
      {:app, replacement} ->
        normalize_lines(rest, prepend(replacement, acc), true)

      {:sup, replacement} ->
        normalize_lines(rest, prepend(replacement, acc), true)

      {:actor, replacement} ->
        {body, tail} = take_declaration_body(rest)
        body = Enum.map(body, &indent_line(&1, 2))
        normalize_lines(tail, prepend(replacement ++ body, acc), true)

      {:fsm, replacement, true} ->
        {body, tail} = take_declaration_body(rest)
        body = body |> Enum.reject(&(&1 == "  pickup")) |> Enum.map(&indent_line(&1, 2))
        normalize_lines(tail, prepend(replacement ++ body, acc), true)

      {:fsm_callback, indent, name} ->
        {body, tail} = take_declaration_body(rest)

        case body do
          [initial_line | _] ->
            case Regex.run(
                   ~r/^\s*fn\s+initial_state\(\)\s+->\s+\S+\s*=\s*(.+)\s*$/,
                   initial_line,
                   capture: :all_but_first
                 ) do
              [initial] ->
                replacement = [
                  "#{indent}fsm #{name}",
                  "#{indent}  state Atom",
                  "#{indent}  initial #{initial}",
                  "#{indent}  event_type Atom",
                  "#{indent}  events",
                  "#{indent}    Tick -> :keep_state_and_data"
                ]

                normalize_lines(tail, prepend(replacement, acc), true)

              _ ->
                normalize_lines(rest, [line | acc], false)
            end

          _ ->
            normalize_lines(rest, [line | acc], false)
        end

      :no_change ->
        normalize_lines(rest, [line | acc], changed)
    end
  end

  defp normalize_header(line) do
    case Regex.run(~r/^(\s*)app\s+(\S+)\s+root\s+(\S+)\s*$/, line, capture: :all_but_first) do
      [indent, name, root] ->
        {:app, ["#{indent}app #{name}", "#{indent}  root #{root}"]}

      _ ->
        normalize_sup(line) || normalize_actor(line) || normalize_fsm(line) || :no_change
    end
  end

  defp normalize_sup(line) do
    case Regex.run(~r/^(\s*)sup\s+(\S+)\s+children\s+\[(.*)\]\s*$/, line, capture: :all_but_first) do
      [indent, name, children] ->
        entries =
          children
          |> String.split(",", trim: true)
          |> Enum.map(&String.trim/1)
          |> Enum.map(fn entry ->
            case Regex.run(~r/^child_spec\s+(\S+)\s+:([A-Za-z_][A-Za-z0-9_]*)$/, entry, capture: :all_but_first) do
              [module, identity] -> "#{indent}    actor #{module} as #{identity}"
              _ -> "#{indent}    #{entry}"
            end
          end)

        {:sup, ["#{indent}sup #{name}", "#{indent}  children" | entries]}

      _ ->
        nil
    end
  end

  defp normalize_actor(line) do
    case Regex.run(~r/^(\s*)actor\s+(\S+)\s+with\s+(.+)\s*$/, line, capture: :all_but_first) do
      [indent, name, initial] ->
        {:actor,
         [
           "#{indent}actor #{name}",
           "#{indent}  state Tuple",
           "#{indent}  initial #{initial}",
           "#{indent}  body"
         ]}

      _ ->
        case Regex.run(
               ~r/^(\s*)actor\s+(\S+)\s+state\s+(.+?)\s+initial\s+(.+?)\s+messages\s+(.+?)\s+handle_cast\s*$/,
               line,
               capture: :all_but_first
             ) do
          [indent, name, state, initial, messages] ->
            {:actor,
             [
               "#{indent}actor #{name}",
               "#{indent}  state #{state}",
               "#{indent}  initial #{initial}",
               "#{indent}  messages #{messages}",
               "#{indent}  handle_cast"
             ]}

          _ ->
            nil
        end
    end
  end

  defp normalize_fsm(line) do
    case Regex.run(
           ~r/^(\s*)fsm\s+(\S+)\s+state\s+(.+?)\s+initial\s+(.+?)\s+events\s+(\S+)\s+transition\s*$/,
           line,
           capture: :all_but_first
         ) do
      [indent, name, state, initial, event_type] ->
        {:fsm,
         [
           "#{indent}fsm #{name}",
           "#{indent}  state #{state}",
           "#{indent}  initial #{initial}",
           "#{indent}  event_type #{event_type}",
           "#{indent}  events"
         ], true}

      _ ->
        case Regex.run(~r/^(\s*)fsm\s+(\S+)(?:\s+with\s+\S+)?\s*$/, line, capture: :all_but_first) do
          [indent, name] ->
            # The old callback-only showcase has no event vocabulary.  Give it
            # the smallest explicit structured shell; the callback's initial
            # state is folded into `initial` when the following line matches.
            {:fsm_callback, indent, name}

          _ ->
            nil
        end
    end
  end

  defp prepend(lines, acc), do: Enum.reduce(lines, acc, &[&1 | &2])

  defp take_declaration_body(lines) do
    Enum.split_while(lines, fn line ->
      line == "" or String.starts_with?(line, " ") or String.starts_with?(line, "\t")
    end)
  end

  defp indent_line("", amount), do: String.duplicate(" ", amount)
  defp indent_line(line, amount), do: String.duplicate(" ", amount) <> line
end
