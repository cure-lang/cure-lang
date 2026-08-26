defmodule Cure.Elab.ComparisonOperatorOrdTest do
  @moduledoc """
  Comparison operators are typeclass overloads resolved through `Std.Comparable` — not
  bespoke `build_binop` cases. `<`/`>`/`<=`/`>=` keep their primitive meaning on
  `Int`/`Float`; on ANY other operand type `build_binop` reports
  `{:unsupported_operand_type, op}` and the elaborator desugars through
  `Std.Comparable.compare`:

      a <  b  ~>  compare(a, b) == LessThan()
      a >  b  ~>  compare(a, b) == GreaterThan()
      a <= b  ~>  compare(a, b) != GreaterThan()
      a >= b  ~>  compare(a, b) != LessThan()

  `compare` then dispatches by coherence to the operand's `Ord` instance. This
  mirrors the `<>`/`+`-> `Std.Semigroup.combine` overload and requires
  `use Std.Comparable` in scope (class-import model).
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  defp eval(src, fname, mod) do
    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [fname])
    {:ok, m} = Emit.compile_and_load(env, module: mod, functions: fns)
    apply(m, fname, [])
  end

  test "`<` on Char routes through Ord.compare (code-point order)" do
    src = """
    mod T
      use Std.Comparable
      use Std.Char
      fn go() -> Bool = 'a' < 'b'
    end
    """

    assert eval(src, :go, :"Cure.CmpCharLt") == true
  end

  test "`>` on Char routes through Ord.compare" do
    src = """
    mod T
      use Std.Comparable
      use Std.Char
      fn go() -> Bool = 'a' > 'b'
    end
    """

    assert eval(src, :go, :"Cure.CmpCharGt") == false
  end

  test "`<=` on Char routes through Ord.compare (reflexive)" do
    src = """
    mod T
      use Std.Comparable
      use Std.Char
      fn go() -> Bool = 'a' <= 'a'
    end
    """

    assert eval(src, :go, :"Cure.CmpCharLe") == true
  end

  test "`>=` on Char routes through Ord.compare" do
    src = """
    mod T
      use Std.Comparable
      use Std.Char
      fn go() -> Bool = 'b' >= 'a'
    end
    """

    assert eval(src, :go, :"Cure.CmpCharGe") == true
  end

  test "`<` on String routes through Ord.compare (lexicographic)" do
    src = """
    mod T
      use Std.Comparable
      use Std.String
      fn go() -> Bool = "ada" < "grace"
    end
    """

    assert eval(src, :go, :"Cure.CmpStrLt") == true
  end

  test "numeric `<`/`>` on Int and Float keep primitive meaning" do
    assert eval("mod T\n  fn go() -> Bool = 2 < 3\nend\n", :go, :"Cure.CmpIntLt") == true
    assert eval("mod T\n  fn go() -> Bool = 5 > 3\nend\n", :go, :"Cure.CmpIntGt") == true
    assert eval("mod T\n  fn go() -> Bool = 2.0 < 3.0\nend\n", :go, :"Cure.CmpFloatLt") == true
  end
end
