defmodule Cure.Stdlib.UnitTypeTest do
  @moduledoc """
  `Std.Unit` — the unit type written the Swift way: `type Unit = ()`, with `()`
  as its sole value. This gives the compiler-seeded unit type a visible, surface
  definition (like `Std.Bool`/`Std.Nat`). `= ()` is reserved to `Unit`: any other
  type declared as `()` is a compile error, and `()` is not usable as a general
  ADT constructor spelling.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Inductive

  defp elab(src) do
    try do
      Cure.Elab.Program.elaborate(src)
    rescue
      e -> {:raise, Exception.message(e)}
    catch
      k, v -> {:raise, "#{inspect(k)}: #{inspect(v)}"}
    end
  end

  test "lib/std/unit.cure elaborates and declares Unit with the nullary `unit` ctor" do
    src = File.read!("lib/std/unit.cure")
    assert {:ok, env} = elab(src)
    ctors = Inductive.ctors_of(env, :Unit)
    assert [%{name: :"Std.Unit#unit", args: []}] = ctors
  end

  test "`type Unit = ()` produces the same family the compiler seeds" do
    {:ok, env} = elab("@group(:core)\nmod Std.Unit\n  type Unit = ()\n")
    assert [%{name: :"Std.Unit#unit", args: []}] = Inductive.ctors_of(env, :Unit)
  end

  test "`()` is a value of type Unit" do
    assert {:ok, _env} = elab("mod U\n  fn u() -> Unit = ()\n")
  end

  test "`type Foo = ()` for a non-Unit name is a reserved-syntax compile error" do
    source = "mod U\n  type Foo = ()\n"
    assert {:error, errors} = elab(source)
    flat = List.wrap(errors)

    assert [{:unit_type_reserved, details} = error] = flat
    assert details.name == "Foo"
    assert details.span.start_line == 2
    assert details.span.start_column == 8
    assert details.span.end_column == 11
    assert details.unit_span.start_column == 14
    assert details.unit_span.end_column == 16

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "unit.cure", source)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- UNIT SYNTAX CANNOT DEFINE ANOTHER TYPE [E092] --------------------- unit.cure

             `()` has exactly one type, `Unit`, so it cannot define the new type `Foo`.

             at unit.cure:2:8
             2 |   type Foo = ()
               |        ^^^   -- this declaration must not reuse `Unit` syntax; this spelling denotes the built-in `Unit` type

             Hint: Give `Foo` its own constructor, or rename the type to `Unit`
             """)

    lsp = Cure.Diagnostic.Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 1, "character" => 7},
             "end" => %{"line" => 1, "character" => 10}
           }

    assert [%{"location" => %{"range" => unit_range}}] = lsp["relatedInformation"]

    assert unit_range == %{
             "start" => %{"line" => 1, "character" => 13},
             "end" => %{"line" => 1, "character" => 15}
           }
  end
end
