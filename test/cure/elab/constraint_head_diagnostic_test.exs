defmodule Cure.Elab.ConstraintHeadDiagnosticTest do
  @moduledoc """
  A constraint head that no argument fixes is read off the expected result type.

  `Std.Json.decode_as(source: String) -> Result(t, DecodeError) requires FromJSON(t)`
  is the canonical shape: `t` is named by the result and by the constraint, never
  by an argument. In checking position the call recovers `t` from the type the
  surrounding context expects.

  When the expected type does not have the declared result's shape there is
  nothing to read `t` off, and the call cannot be resolved. That is an ordinary
  authoring mistake — the annotation is too loose, or is simply the wrong type —
  so it must read as one. It used to escape elaboration as a bare
  `{:constraint_head_not_determined, iface, tyvar}` with no registered
  conversion, surfacing as `INTERNAL COMPILER ERROR [E101]` and a report
  fingerprint, which tells the author nothing and invites a bug report for their
  own typo.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.{Renderer, Sink}

  @source """
  mod DecodeExample
    use Std.Result
    use Std.Json

    fn flag() -> Bool =
      assert_type decode_as("true") : Bool
  end
  """

  defp diagnose(source) do
    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "decode.cure", emit_events: false)

    Errors.to_diagnostic(reason, "decode.cure", source)
  end

  test "an undetermined constraint head is a real diagnostic, not an internal error" do
    {diagnostic, registry} = diagnose(@source)

    assert diagnostic.code == "E093"
    refute diagnostic.code == "E101"

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    # Every fact the author needs: which call, which constraint, which type
    # variable, why it is unfixed, and what the expected type actually was.
    assert rendered =~ "decode_as"
    assert rendered =~ "FromJSON"
    assert rendered =~ "`t`"
    assert rendered =~ "Bool"

    # And the shape the annotation has to take for `t` to be determined.
    assert rendered =~ "Result(t, DecodeError)"

    refute rendered =~ "INTERNAL COMPILER ERROR"
    refute rendered =~ "fingerprint"
  end

  test "the payload carries the constraint machinery for tooling" do
    {diagnostic, _registry} = diagnose(@source)

    assert diagnostic.payload.kind == :constraint_head_not_determined
    assert diagnostic.payload.interface == :FromJSON
    assert diagnostic.payload.type_variable == "t"
    assert diagnostic.payload.callee == :decode_as
    assert diagnostic.payload.expected_surface =~ "Bool"
    assert diagnostic.payload.result_surface == "Result(t, DecodeError)"
  end

  test "the failure is located at the call and projects through every renderer" do
    {diagnostic, registry} = diagnose(@source)

    assert %Cure.Diagnostic.Label{span: span} = diagnostic.primary
    assert span.start_line == 6

    terminal = Renderer.terminal(diagnostic, registry, color: :always, width: 80)
    json = diagnostic |> Renderer.json() |> Jason.decode!()
    lsp = Sink.render(Sink.new(format: :lsp, registry: registry, position_encoding: :utf16), diagnostic)

    assert terminal =~ "\e["
    assert json["code"] == "E093"
    assert lsp["code"] == "E093"
    assert lsp["range"]["start"]["line"] == 5
  end

  test "a result annotation that does fix the head still resolves" do
    source = """
    mod DecodeExample
      use Std.Result
      use Std.Json

      fn flag() -> Result(Bool, DecodeError) =
        assert_type decode_as("true") : Result(Bool, DecodeError)
    end
    """

    assert {:ok, _module, _warnings} =
             Cure.Compiler.compile_string(source, file: "decode_ok.cure", emit_events: false)
  end
end
