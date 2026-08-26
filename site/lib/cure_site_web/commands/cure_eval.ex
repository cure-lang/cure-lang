defmodule CureSiteWeb.Commands.CureEval do
  @moduledoc """
  Yeesh command that compiles and evaluates a Cure expression or module snippet.

  Wraps `Cure.Compiler.compile_and_load/2` so the error-page terminal behaves
  like a lightweight `cure repl` session.  Plain expressions are wrapped in a
  throw-away module before being handed to the compiler.
  """

  alias Cure.Diagnostic.{Host, Operational}

  @behaviour Yeesh.Command

  @impl true
  def name, do: "eval"

  @impl true
  def group, do: "Cure"

  @impl true
  def description, do: "Compile and evaluate a Cure expression"

  @impl true
  def usage, do: "eval <cure_expression>"

  @impl true
  def completions(_partial, _session), do: []

  @impl true
  def execute([], session) do
    {:error, "Usage: eval <cure_expression>", session}
  end

  def execute(args, session) do
    source = Enum.join(args, " ")

    result =
      if looks_like_module?(source) do
        compile_module(source)
      else
        compile_expr(source)
      end

    case result do
      {:ok, output} -> {:ok, output, session}
      {:error, msg} -> {:error, msg, session}
    end
  end

  # ---------------------------------------------------------------------------

  defp looks_like_module?(source) do
    String.match?(source, ~r/^\s*(mod|type|fn|rec|sup|actor|app)\s/)
  end

  defp compile_module(source) do
    case Cure.Compiler.compile_and_load(source, file: "repl", check_types: false) do
      {:ok, mod} ->
        {:ok, "Loaded: #{inspect(mod)}"}

      {:error, reason} ->
        {:error, format_error(reason, source)}
    end
  end

  defp compile_expr(source) do
    # Wrap bare expression in a minimal module so the compiler accepts it.
    wrapped = """
    mod __ReplExpr__
      fn __run__() -> _ = #{source}
    """

    case Cure.Compiler.compile_and_load(wrapped, file: "repl", check_types: false) do
      {:ok, mod} ->
        result =
          try do
            apply(mod, :__run__, []) |> inspect()
          rescue
            e -> render_exception(e, __STACKTRACE__)
          end

        {:ok, "=> #{result}"}

      {:error, reason} ->
        {:error, format_error(reason, wrapped)}
    end
  end

  defp format_error(reason, source) do
    Cure.Diagnostic.Host.render(reason, "repl.cure", source)
  end

  defp render_exception(exception, stacktrace) do
    exception
    |> Operational.internal_exception(stacktrace, context: "site eval")
    |> Host.render_diagnostic(color: :never)
  end
end
