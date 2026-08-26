defmodule Mix.Tasks.Cure.Diagnostics do
  use Mix.Task

  @shortdoc "Exercise compiler diagnostics and print them with coverage"

  @moduledoc """
  Runs the diagnostic exerciser under ExUnit coverage. Use:

      mix cure.diagnostics

  Every case is rendered to stderr in the same format used for users. Pass
  `--audit` (normally via `mix cure.diagnostics.audit`) to print a numbered,
  machine-readable header before every fixture as well.
  """

  @impl true
  def run(args) do
    validate_registry!()

    {opts, [], invalid} =
      OptionParser.parse(args,
        strict: [color: :string, width: :integer, coverage: :boolean, audit: :boolean],
        aliases: [w: :width]
      )

    if invalid != [], do: Mix.raise("invalid cure.diagnostics options: #{inspect(invalid)}")

    color =
      case Keyword.get(opts, :color, "auto") do
        value when value in ["auto", "always", "never"] -> String.to_atom(value)
        value -> Mix.raise("invalid --color=#{value}; expected auto, always, or never")
      end

    width = Keyword.get(opts, :width, 80)
    if not is_integer(width) or width < 1, do: Mix.raise("--width must be a positive integer")

    Application.put_env(:cure, :diagnostics_exerciser,
      color: color,
      width: width,
      coverage: Keyword.get(opts, :coverage, false),
      audit: Keyword.get(opts, :audit, false)
    )

    test_args =
      if Keyword.get(opts, :coverage, false),
        do: ["--cover", "test/cure/diagnostic_exerciser_test.exs"],
        else: ["test/cure/diagnostic_exerciser_test.exs"]

    Mix.Task.run("test", test_args)
  end

  defp validate_registry! do
    with :ok <- Cure.Diagnostic.Registry.validate(),
         :ok <- Cure.Diagnostic.Registry.validate_reachability(),
         :ok <- Cure.Diagnostic.Registry.validate_sources(),
         :ok <- Cure.MetaAST.MetadataLint.validate(metadata_semantic_paths()),
         :ok <- validate_inventory() do
      :ok
    else
      {:error, reason} -> Mix.raise("diagnostic registry validation failed: #{inspect(reason)}")
    end
  end

  defp metadata_semantic_paths do
    Path.wildcard("lib/cure/**/*.ex")
  end

  defp validate_inventory do
    inventory = Cure.Diagnostic.Registry.Inventory.scan()

    cond do
      inventory.error_constructors == [] -> {:error, :empty_producer_inventory}
      inventory.deliberate_raises == [] -> {:error, :empty_raise_inventory}
      inventory.formatter_consumers == [] -> {:error, :empty_formatter_inventory}
      inventory.stderr_sites == [] -> {:error, :empty_stderr_inventory}
      true -> Cure.Diagnostic.Registry.Inventory.validate(inventory)
    end
  end
end
