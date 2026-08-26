defmodule Cure.Diagnostic.WarningSnapshotTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Operational, Renderer, SourceRegistry}

  @width 80
  @source "mod Demo\n  fn id(x: T) -> T = x\n"

  setup do
    registry =
      SourceRegistry.new()
      |> SourceRegistry.register("warning.cure", @source, "warning.cure")

    {:ok, span} = SourceRegistry.span_at(registry, "warning.cure", 2, 11, 1)
    {:ok, registry: registry, span: span}
  end

  test "W001 has fixed-width plain and ANSI snapshots plus JSON/LSP parity", %{
    registry: registry,
    span: span
  } do
    diagnostic =
      Operational.migration_warning(%{
        rule: :uppercase_type_var,
        file: "warning.cure",
        line: 2,
        message: "uppercase type variable can be lowercased",
        span: span
      })

    plain =
      """
      -- MIGRATION WARNING [W001] --------------------------------------- warning.cure

      uppercase type variable can be lowercased

      at warning.cure:2:11
      2 |   fn id(x: T) -> T = x
        |           ^ deprecated syntax appears here
      """
      |> String.trim_trailing()

    ansi =
      IO.ANSI.cyan() <>
        "-- MIGRATION WARNING [W001] --------------------------------------- warning.cure" <>
        IO.ANSI.reset() <>
        "\n\nuppercase type variable can be lowercased\n\nat warning.cure:2:11\n" <>
        "2 |   fn id(x: T) -> T = x\n  |           " <>
        IO.ANSI.yellow() <> "^" <> IO.ANSI.reset() <> " deprecated syntax appears here"

    assert Renderer.plain(diagnostic, registry, width: @width) == plain
    assert Renderer.terminal(diagnostic, registry, width: @width, color: :always) == ansi

    assert_projection_snapshot(diagnostic, registry,
      code: "W001",
      key: "migration_warning",
      payload: %{"file" => "warning.cure", "line" => 2, "rule" => "uppercase_type_var"},
      message: "Migration warning\n\nuppercase type variable can be lowercased",
      range: range(1, 10, 1, 11)
    )
  end

  test "W000 has fixed-width plain and ANSI snapshots plus JSON/LSP parity", %{
    registry: registry,
    span: span
  } do
    diagnostic =
      Operational.compiler_warning(%{
        file: "warning.cure",
        line: 2,
        message: "this definition is deprecated",
        span: span
      })

    plain =
      """
      -- COMPILER WARNING [W000] ---------------------------------------- warning.cure

      this definition is deprecated

      at warning.cure:2:11
      2 |   fn id(x: T) -> T = x
        |           ^ compiler warning applies here
      """
      |> String.trim_trailing()

    ansi =
      IO.ANSI.cyan() <>
        "-- COMPILER WARNING [W000] ---------------------------------------- warning.cure" <>
        IO.ANSI.reset() <>
        "\n\nthis definition is deprecated\n\nat warning.cure:2:11\n" <>
        "2 |   fn id(x: T) -> T = x\n  |           " <>
        IO.ANSI.yellow() <> "^" <> IO.ANSI.reset() <> " compiler warning applies here"

    assert Renderer.plain(diagnostic, registry, width: @width) == plain
    assert Renderer.terminal(diagnostic, registry, width: @width, color: :always) == ansi

    assert_projection_snapshot(diagnostic, registry,
      code: "W000",
      key: "compiler_warning",
      payload: %{"file" => "warning.cure", "line" => 2},
      message: "Compiler warning\n\nthis definition is deprecated",
      range: range(1, 10, 1, 11)
    )
  end

  test "global W002 and W003 warnings have fixed-width snapshots and no invented LSP range", %{
    registry: registry
  } do
    cases = [
      {Operational.configuration_warning("invalid setting"),
       "-- INVALID CONFIGURATION [W002] ------------------------------------------------\n\ninvalid setting",
       "configuration_warning", %{}, "Invalid configuration\n\ninvalid setting"},
      {Operational.destructive_format_warning(),
       "-- FORMATTING MAY DISCARD SOURCE DETAILS [W003] --------------------------------\n\n" <>
         "`cure fmt --aggressive` rebuilds source from the AST, so plain `#` comments and\n" <>
         "non-canonical whitespace may be removed.\n\n" <>
         "Note: Commit or copy these files before continuing.", "destructive_format_warning", %{"mode" => "aggressive"},
       "Formatting may discard source details\n\n" <>
         "`cure fmt --aggressive` rebuilds source from the AST, so plain `#` comments and non-canonical whitespace may be removed."}
    ]

    for {diagnostic, plain, key, payload, message} <- cases do
      assert Renderer.plain(diagnostic, registry, width: @width) == plain

      [header | rest] = String.split(plain, "\n")
      ansi = IO.ANSI.cyan() <> header <> IO.ANSI.reset() <> "\n" <> Enum.join(rest, "\n")
      assert Renderer.terminal(diagnostic, registry, width: @width, color: :always) == ansi

      assert_projection_snapshot(diagnostic, registry,
        code: diagnostic.code,
        key: key,
        payload: payload,
        message: message,
        range: nil
      )
    end
  end

  defp assert_projection_snapshot(diagnostic, registry, expected) do
    json = Jason.decode!(Renderer.json(diagnostic))
    lsp = Renderer.lsp(diagnostic, registry)

    assert json["code"] == expected[:code]
    assert json["key"] == expected[:key]
    assert json["severity"] == "warning"
    assert json["payload"] == expected[:payload]
    assert json["primary"] == json_primary(expected[:range], expected[:code])

    assert lsp ==
             %{
               "code" => expected[:code],
               "data" => %{
                 "key" => expected[:key],
                 "payload" => expected[:payload],
                 "provenance" => [],
                 "suggestions" => []
               },
               "message" => expected[:message],
               "relatedInformation" => [],
               "severity" => 2,
               "source" => "cure"
             }
             |> maybe_put_range(expected[:range])
  end

  defp json_primary(nil, _code), do: nil

  defp json_primary(_range, code) do
    %{
      "message" => if(code == "W001", do: "deprecated syntax appears here", else: "compiler warning applies here"),
      "span" => %{
        "source_id" => "warning.cure",
        "path" => "warning.cure",
        "start_byte" => 19,
        "end_byte" => 20,
        "start_line" => 2,
        "start_column" => 11,
        "end_line" => 2,
        "end_column" => 12
      },
      "style" => "primary"
    }
  end

  defp range(sl, sc, el, ec) do
    %{
      "start" => %{"line" => sl, "character" => sc},
      "end" => %{"line" => el, "character" => ec}
    }
  end

  defp maybe_put_range(map, nil), do: map
  defp maybe_put_range(map, range), do: Map.put(map, "range", range)
end
