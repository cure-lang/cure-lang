defmodule Cure.Types.Holes do
  @moduledoc """
  Hole-driven development support for the Cure type system.

  A *hole* is a placeholder for an as-yet-unwritten expression that
  the type checker should *report on*, not silently accept. Holes
  come in two flavours:

  - **Named hole** `?name` -- carries a label the user picks. The
    checker reports the goal type and the local context.
  - **Anonymous hole** `?_` -- like a named hole but unlabelled. When
    the same source contains many `?_`, they are numbered `?_1`,
    `?_2`, ... in source order.

  ## Representation

  At the type-checker level, a hole is `{:hole, name :: String.t(), ctx :: map()}`
  where `ctx` maps in-scope variable names to their inferred types
  at the hole position.

  ## Reporting

  When the checker visits a hole, it emits a `:hole_goal` pipeline
  event:

      Events.emit(:type_checker, :hole_goal, {name, goal, ctx}, meta)

  Subscribers (LSP, REPL, CLI) render the goal and context.

  ## Surface syntax

  Today, two surface forms are recognised by the lexer/parser layer:

  - `_` in any *type-annotation* position becomes the legacy
    `{:type_hole, :infer}` (silenced subtype rule).
  - `?name` and `?_` in any *value* position become a `{:hole, meta, []}`
    node that this module detects and converts.

  ## Workflow

  ```
  fn safe_head(xs: List(T)) -> T = ?body
  ```

  Compiling reports:

      ?body : T   in scope: xs : List(T)

  The user fills in the hole and re-runs.
  """

  alias Cure.Pipeline.Events

  @type ctx :: %{optional(String.t()) => term()}
  @type t :: {:hole, String.t(), ctx()}

  # -- Construction ------------------------------------------------------------

  @doc "Build a hole."
  @spec new(String.t(), ctx()) :: t()
  def new(name, ctx) when is_binary(name), do: {:hole, name, ctx}

  @doc "True when `t` is a hole."
  @spec hole?(term()) :: boolean()
  def hole?({:hole, _n, _c}), do: true
  def hole?(_), do: false

  @doc "Hole name."
  @spec name(t()) :: String.t()
  def name({:hole, n, _}), do: n

  @doc "Hole context."
  @spec context(t()) :: ctx()
  def context({:hole, _n, c}), do: c

  @doc """
  Recognise hole-shaped AST nodes produced by the parser/lexer.

  Returns `{:hole, name}` for `?name`, `{:hole, :anon}` for `?_`,
  and `:not_a_hole` otherwise.
  """
  @spec recognise(tuple()) :: {:hole, String.t()} | {:hole, :anon} | :not_a_hole
  def recognise({:hole, meta, []}) do
    case Keyword.get(meta, :name, "") do
      "_" -> {:hole, :anon}
      "?" -> {:hole, :anon}
      name when is_binary(name) and name != "" -> {:hole, name}
      _ -> :not_a_hole
    end
  end

  def recognise({:variable, _meta, "?_"}), do: {:hole, :anon}
  def recognise({:variable, _meta, "_"}), do: {:hole, "_"}

  def recognise({:variable, _meta, <<"?", rest::binary>>}) when rest != "" do
    {:hole, rest}
  end

  def recognise({:function_call, meta, []}) do
    case Keyword.get(meta, :name, "") do
      "?_" -> {:hole, :anon}
      <<"?", rest::binary>> when rest != "" -> {:hole, rest}
      _ -> :not_a_hole
    end
  end

  def recognise(_), do: :not_a_hole

  @doc """
  Report a hole through the pipeline event system.
  """
  @spec report(String.t() | :anon, term(), ctx(), String.t(), pos_integer()) :: :ok
  def report(name, goal, ctx, file, line) do
    label = if name == :anon, do: "?_", else: "?#{name}"
    Events.emit(:type_checker, :hole_goal, {label, goal, ctx}, Events.meta(file, line))
  end

  @doc """
  Render a hole report as a human-readable string.
  """
  @spec render(String.t(), term(), ctx()) :: String.t()
  def render(label, goal, ctx) do
    goal_str = format_goal(goal)

    ctx_lines =
      ctx
      |> Enum.sort()
      |> Enum.map(fn {var, type} -> "  #{var} : #{display_type(type)}" end)
      |> Enum.join("\n")

    """
    #{label} : #{goal_str}
    in scope:
    #{if ctx_lines == "", do: "  (empty)", else: ctx_lines}
    """
  end

  defp format_goal(goal) when is_atom(goal) or is_tuple(goal), do: display_type(goal)
  defp format_goal(other), do: inspect(other)

  defp display_type(type) when is_binary(type), do: type
  defp display_type(type) when is_atom(type), do: Atom.to_string(type)

  defp display_type(type) do
    Cure.Core.Printer.print(type)
  rescue
    ArgumentError -> inspect(type)
  end

  @doc """
  Walk an AST and number anonymous holes in source order.

  Returns the AST with `?_` replaced by `?_1`, `?_2`, ...
  """
  @spec number_anonymous(tuple()) :: tuple()
  def number_anonymous(ast) do
    {ast, _counter} = walk_number(ast, 1)
    ast
  end

  defp walk_number({:hole, meta, []}, n) do
    case Keyword.get(meta, :name) do
      "_" -> {{:hole, Keyword.put(meta, :name, "_#{n}"), []}, n + 1}
      _ -> {{:hole, meta, []}, n}
    end
  end

  defp walk_number({:variable, meta, "?_"}, n) do
    {{:variable, meta, "?_#{n}"}, n + 1}
  end

  defp walk_number({:function_call, meta, []}, n) do
    case Keyword.get(meta, :name, "") do
      "?_" ->
        new_meta = Keyword.put(meta, :name, "?_#{n}")
        {{:function_call, new_meta, []}, n + 1}

      _ ->
        {{:function_call, meta, []}, n}
    end
  end

  defp walk_number({tag, meta, children}, n) when is_list(children) do
    {new_children, new_n} =
      Enum.map_reduce(children, n, fn child, acc ->
        walk_number(child, acc)
      end)

    {{tag, meta, new_children}, new_n}
  end

  defp walk_number(other, n), do: {other, n}
end
