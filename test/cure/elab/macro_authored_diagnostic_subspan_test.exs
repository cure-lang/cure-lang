defmodule Cure.Elab.MacroAuthoredDiagnosticSubspanTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Elab.Program

  test "an authored diagnostic can safely select a relative range inside captured syntax" do
    source = """
    mod M
      use Std.Syntax

      macro Mark
        syntax mark <value: Expression> computed by diagnose

      fn diagnose(input: Syntax) -> MacroResult = match children(input)
        [value] -> reject(Failure(:bad_fragment, [diagnostic_subspan(value, 1, 2)]))
        _ -> reject(Failure(:bad_input, []))

      fn f(alpha: Int) -> Int = mark alpha
    """

    assert {:error,
            {:source_context,
             {:computed_macro_error, _meta, {:author_diagnostics, [{:macro_failure, :bad_fragment, [_selector]}]}},
             _context} = reason} =
             Program.elaborate(source)

    {diagnostic, _registry} = Errors.to_diagnostic(reason, "diagnostic_subspan.cure", source)
    span = diagnostic.primary.span

    assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == "lp"
    assert diagnostic.payload.reason.names == ["bad_fragment"]
  end

  test "an out-of-range selector cannot escape its captured syntax" do
    source = """
    mod M
      use Std.Syntax

      macro Mark
        syntax mark <value: Expression> computed by diagnose

      fn diagnose(input: Syntax) -> MacroResult = match children(input)
        [value] -> reject(Failure(:bad_fragment, [diagnostic_subspan(value, 99, 2)]))
        _ -> reject(Failure(:bad_input, []))

      fn f(alpha: Int) -> Int = mark alpha
    """

    assert {:error, reason} = Program.elaborate(source)
    {diagnostic, _registry} = Errors.to_diagnostic(reason, "diagnostic_subspan.cure", source)
    span = diagnostic.primary.span

    assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == "mark alpha"
  end
end
