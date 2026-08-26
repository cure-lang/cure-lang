defmodule Cure.Compiler.Parser.FixityScanTest do
  use ExUnit.Case, async: true
  alias Cure.Compiler.Parser.{FixityScan, BuiltinFixity, FixityTable}

  @src """
  @prelude
  mod M
    use Std.Operators
    use Other.Mod
    precedencegroup G
      associativity: left
    infix `<?>` : G
    fn go() -> Int = 1 <?> 2
  end
  """

  defp scan(src), do: FixityScan.harvest_source(src, "m.cure", BuiltinFixity.table())

  test "extracts fixity + precedencegroup nodes despite a body using <?>" do
    s = scan(@src)
    ops = for {:fixity, meta, _} <- s.fixity, do: Keyword.get(meta, :operator)
    groups = for {:precedencegroup, meta, _} <- s.fixity, do: Keyword.get(meta, :name)
    assert "<?>" in ops
    assert :G in groups
  end

  test "extracts use targets" do
    targets = Enum.map(scan(@src).uses, & &1.target)
    assert "Std.Operators" in targets
    assert "Other.Mod" in targets
  end

  test "detects @prelude and module name" do
    s = scan(@src)
    assert s.prelude? == true
    assert s.module == "M"
  end

  test "qualified applied types retain the canonical explicitly used module" do
    source = """
    mod M
      use Std.Otp.Raw
      typealias Selector(p) = Std.Otp.Raw.Selector(p)
    """

    assert scan(source).qualified_targets == [%{target: "Std.Otp.Raw", line: 3}]
  end

  test "qualified type references participate in dependency discovery" do
    source = "mod Cycle.TypeA\n  type A = MkA(Cycle.TypeB.B)\n"

    assert scan(source).qualified_targets == [%{target: "Cycle.TypeB", line: 2}]
  end

  test "a lexer error yields the empty scan rather than raising" do
    s = FixityScan.harvest_source(~s|mod M\n  fn f() = "unterminated|, "m.cure", FixityTable.new())

    assert s == %{
             fixity: [],
             uses: [],
             qualified_targets: [],
             prelude?: false,
             module: nil
           }
  end
end
