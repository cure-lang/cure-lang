defmodule Cure.Elab.StringEqualityTest do
  @moduledoc """
  Equality on `String` (= `List(Char)`) and `Char` (= `Bounded(0x110000)`)
  values. Both erase to native BEAM terms (a char is an integer codepoint, a
  string a list of them), so `==` routes through the polymorphic `struct_eq`
  builtin (BEAM `==`) and compares structurally — no bespoke `string_eq` needed.

  This also pins that `Program.reachable_def_names/2` excludes TYPE-LEVEL defs
  (a type alias like `Char`, whose `type` is `{:type, _}`): they are referenced
  from value bodies only in type positions (lambda domains) and must never be
  handed to emit as runtime functions.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.{Program, Emit}

  test "reachable_def_names excludes type-level defs (type aliases)" do
    {:ok, env} = Program.elaborate("mod M\n  use Std.Char\n  fn eqc(a: Char, b: Char) -> Bool = a == b\nend\n")
    roots = Program.reachable_def_names(env, [:eqc])
    assert :"M#eqc" in roots
    refute :"Std.Char#Char" in roots
  end

  test "Char equality runs end-to-end via struct_eq" do
    {:ok, env} = Program.elaborate("mod M\n  use Std.Char\n  fn eqc(a: Char, b: Char) -> Bool = a == b\nend\n")
    fns = Program.reachable_def_names(env, [:eqc])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.CharEq", functions: fns)
    assert apply(m, :eqc, [?a, ?a]) == true
    assert apply(m, :eqc, [?a, ?b]) == false
  end

  test "String equality runs end-to-end via struct_eq" do
    src = """
    mod M
      use Std.List
      use Std.Char
      fn streq(a: List(Char), b: List(Char)) -> Bool = a == b
    """

    {:ok, env} = Program.elaborate(src)
    fns = Program.reachable_def_names(env, [:streq])
    {:ok, m} = Emit.compile_and_load(env, module: :"Cure.StrEq", functions: fns)
    assert apply(m, :streq, [~c"hi", ~c"hi"]) == true
    assert apply(m, :streq, [~c"hi", ~c"no"]) == false
    assert apply(m, :streq, [~c"", ~c""]) == true
  end
end
