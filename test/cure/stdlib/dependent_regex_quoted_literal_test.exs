defmodule Cure.Stdlib.DependentRegexQuotedLiteralTest do
  use ExUnit.Case, async: false

  setup_all do
    source = ~S"""
    mod RegexQuotedLiteral
      use Std.Regex

      fn quoted_meta() -> Bool = matches(/\Q[a-z]+\E/, "[a-z]+")
      fn quoted_meta_is_literal() -> Bool = not matches(/\Q[a-z]+\E/, "aaaa")
      fn quote_to_end() -> Bool = matches(/\Qabc/, "abc")
      fn literal_terminator() -> Bool = matches(/\Qfoo\E\\E\Qbar\E/, "foo\\Ebar")
    end
    """

    assert {:ok, runtime_module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    {:ok, runtime_module: runtime_module}
  end

  test "quoted regions normalize metacharacters to an exact literal sequence", %{runtime_module: module} do
    assert apply(module, :quoted_meta, [])
    assert apply(module, :quoted_meta_is_literal, [])
  end

  test "an unterminated quoted region extends to the end of the pattern", %{runtime_module: module} do
    assert apply(module, :quote_to_end, [])
  end

  test "a literal backslash-E can follow a closed quoted region", %{runtime_module: module} do
    assert apply(module, :literal_terminator, [])
  end
end
