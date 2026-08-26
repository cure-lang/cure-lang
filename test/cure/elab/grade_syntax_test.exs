defmodule Cure.Elab.GradeSyntaxTest do
  @moduledoc """
  Slice 5a: surface syntax for QTT grades on function parameters.

  The grade is a decorator immediately before the complete binder:

      fn run({@erased n : Nat}, @linear c : Chan(Cmd), @affine h : Handle, budget: Int)

  An absent grade means `ω` — so every existing program is unchanged, and there is
  exactly ONE spelling of each grade (no `:unrestricted` keyword, no numerals).

  ## Why decorators, and why before the name

  The grade is a property of the **arrow**, not of the parameter's name and not of
  its type: Core spells it `{:pi, g, dom, cod}`, and `Conv` compares `g` as part of
  the Pi while `dom` is an ordinary type (`conv.ex:124`). `(1 c : Chan) -> Chan` and
  `(c : Chan) -> Chan` are different function types over the *same* `Chan`. So
  `linear c` (which decorates the name) and `c: linear Chan` (which would make
  `linear Chan` a type Cure has no former for) are both misleading. `@linear c : Chan`
  decorates the binding.

  Idris spells its quantities as bare numerals (`Parser.idr:647-653`), and Cure
  cannot: `fn f(x: 1) -> Int` already parses, with `1` as a literal type, so `:1`
  collides with real syntax; `?` is already the hole token, so `1?` would overload
  it; and Idris has **no affine grade** to port a spelling from in the first place.
  `@erased`, `@linear`, and `@affine` are parsed in the binder grammar, so they
  cannot be confused with type annotations or declaration-level decorators.

  ## What this slice does and does not do

  The grade lands in the def's `quantities` vector, which is what `Relevance`
  (usage check), `Erase`, `Emit`, and `Relevance`'s callee-scaling all read. It does
  **not** yet land in the def's Pi binder: `wrap_binders/3` hardcodes `ω`, so a
  graded function's *type* does not advertise its grade. That is pre-existing —
  erased implicits already have `quantities: [:erased]` with an `ω` Pi — and it is
  tracked as its own slice, because `sig.pi` is built from the original quantities
  while the λ is built from the *demoted* ones (`demote_unused_dicts/3`), so making
  the Pi truthful puts those two in conflict.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler
  alias Cure.Core.Env
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  defp params(src) do
    {:ok, ast} = Compiler.parse_source(src)
    ast |> find_fn() |> elem(1)
  end

  # Pull the first `:function_def`'s params out of the module block.
  defp find_fn(node) do
    case node do
      {:function_def, meta, _} = f -> {f, Keyword.get(meta, :params, [])}
      list when is_list(list) -> list |> Enum.find_value(&maybe_fn/1)
      {_t, _m, children} when is_list(children) -> children |> Enum.find_value(&maybe_fn/1)
      _ -> nil
    end
  end

  defp maybe_fn(node), do: find_fn(node)

  defp grades(src), do: params(src) |> Enum.map(fn {:param, m, n} -> {n, Keyword.get(m, :grade)} end)

  defp quantities(src) do
    {:ok, env} = Program.semantic_result(Program.elaborate(src))
    env |> Env.get_def(:f) |> Map.fetch!(:quantities)
  end

  describe "the parser records a grade at the binding site" do
    test "an explicit linear parameter" do
      assert [{"c", :linear}] = grades("mod G\n  fn f(@linear c : Int) -> Int = c\nend\n")
    end

    test "an explicit affine parameter" do
      assert [{"h", :affine}] = grades("mod G\n  fn f(@affine h : Int) -> Int = 0\nend\n")
    end

    test "an explicit erased parameter" do
      assert [{"n", :erased}] = grades("mod G\n  fn f(@erased n : Int) -> Int = 0\nend\n")
    end

    test "an implicit parameter carries the grade INSIDE the brace" do
      src = "mod G\n  fn f({@erased n : Int}, x: Int) -> Int = x\nend\n"
      assert [{"n", :erased}, {"x", nil}] = grades(src)
    end

    test "an ungraded parameter records no grade — absent means omega" do
      assert [{"x", nil}] = grades("mod G\n  fn f(x: Int) -> Int = x\nend\n")
    end

    test "grades mix freely with ungraded parameters" do
      src = "mod G\n  fn f(@linear c : Int, x: Int, @affine h : Int) -> Int = c\nend\n"
      assert [{"c", :linear}, {"x", nil}, {"h", :affine}] = grades(src)
    end
  end

  describe "there is exactly ONE spelling of each grade" do
    test "@unrestricted is NOT a spelling — omega is written by omission" do
      assert {:error, _} = Compiler.parse_source("mod G\n  fn f(@unrestricted x : Int) -> Int = x\nend\n")
    end

    test "an unknown grade decorator is a parse error, never a silently ignored annotation" do
      assert {:error, _} = Compiler.parse_source("mod G\n  fn f(@bogus x : Int) -> Int = x\nend\n")
    end

    test "a graded parameter must still have a type" do
      assert {:error, _} = Compiler.parse_source("mod G\n  fn f(@linear c :) -> Int = 0\nend\n")
    end

    test "`x: 1` still parses as a literal type annotation — no numeral collision" do
      assert {:ok, _} = Compiler.parse_source("mod G\n  fn f(x: 1) -> Int = 0\nend\n")
    end
  end

  describe "the grade reaches the def's quantities vector" do
    test "an explicit grade overrides the omega default" do
      assert [:linear] = quantities("mod G\n  fn f(@linear c : Int) -> Int = c\nend\n")
    end

    test "an explicit grade overrides the erased default on an implicit" do
      # `c` must be consumed by a LINEAR position — handing it to `plus`'s omega
      # parameter would scale it to omega and (correctly) break the obligation.
      src = "mod G\n  fn sink(@linear y : Int) -> Int = y\n  fn f({@linear c : Int}, x: Int) -> Int = sink(c)\nend\n"
      assert [:linear, :unrestricted] = quantities(src)
    end

    test "an ungraded implicit is still erased, an ungraded explicit still omega" do
      assert [:erased, :unrestricted] = quantities("mod G\n  fn f({a: Type}, x: a) -> a = x\nend\n")
    end
  end

  describe "the usage check enforces the declared grade end to end" do
    test "a linear parameter used exactly once is accepted" do
      assert {:ok, _} = Program.elaborate("mod G\n  fn f(@linear c : Int) -> Int = c\nend\n")
    end

    test "a linear parameter used zero times is REJECTED" do
      assert {:error, {:usage_violation, %{declared: :linear, used: :erased}}} =
               Program.semantic_result(Program.elaborate("mod G\n  fn f(@linear c : Int) -> Int = 0\nend\n"))
    end

    test "an affine parameter used zero times is accepted" do
      assert {:ok, _} = Program.elaborate("mod G\n  fn f(@affine h : Int) -> Int = 0\nend\n")
    end

    test "a linear parameter passed to an unrestricted position is REJECTED" do
      # `use` declares `x` at omega, so `mul(omega, linear) = omega` and the linear
      # obligation is broken. This is the callee-scaling half of the usage check.
      src = "mod G\n  fn use2(x: Int) -> Int = x\n  fn f(@linear c : Int) -> Int = use2(c)\nend\n"

      assert {:error, {:usage_violation, %{declared: :linear, used: :unrestricted}}} =
               Program.semantic_result(Program.elaborate(src))
    end

    test "a linear parameter passed to a LINEAR position is accepted" do
      src = "mod G\n  fn sink(@linear x : Int) -> Int = x\n  fn f(@linear c : Int) -> Int = sink(c)\nend\n"
      assert {:ok, _} = Program.semantic_result(Program.elaborate(src))
    end

    test "a global application accepts a linear explicit parameter" do
      src =
        "mod Cure.LinearGlobalCall\n  fn sink(@linear value : Int) -> Int = value\n  fn use(value: Int) -> Int = sink(value)\nend\n"

      assert {:ok, _} = Compiler.compile_and_load(src, emit_events: false)
    end
  end

  describe "extern arity counts PRESENT parameters, not unrestricted ones" do
    # `check_extern_arity/2` asks `q == :unrestricted`, the same slice-4a trap that
    # was fixed in `Erase`/`Emit`/`Relevance`. A `:linear` parameter is present at
    # runtime, so it must be counted. Otherwise `@extern(:m, :f, 1)` on a def with
    # one linear parameter is rejected as an arity mismatch against a computed 0.
    test "an extern with a linear parameter accepts its true present arity" do
      src = "mod G\n  @extern(:erlang, :abs, 1)\n  fn f(@linear c : Int) -> Int\nend\n"
      assert {:ok, _} = Program.semantic_result(Program.elaborate(src))
    end

    test "an extern with an erased implicit still excludes it from the arity" do
      src = "mod G\n  @extern(:erlang, :hd, 1)\n  fn f({a: Type}, xs: List(a)) -> a\nend\n"
      assert {:ok, _} = Program.semantic_result(Program.elaborate(src))
    end
  end

  describe "grade errors NAME the problem (adversarial review F6/F8)" do
    # These programs were already REJECTED — but with a `{:expected, :rparen, …}`
    # cascade that says nothing about the grade. A grade is a deliberate annotation;
    # a mistake in it deserves a diagnostic that points at the grade, not at a
    # downstream token the real error desynced onto.
    defp errors(src) do
      {:error, {:parse_error, errs}} = Compiler.parse_source(src)
      errs
    end

    defp diagnostic(src, file \\ "grade.cure") do
      assert {:error, reason} = Compiler.parse_source(src, file: file)
      Cure.Compiler.Errors.to_diagnostic(reason, file, src)
    end

    test "a grade with a missing required type names the grade, not `expected rparen`" do
      errs = errors("mod G\n  fn f(@linear c :) -> Int = 0\nend\n")

      assert Enum.any?(errs, &match?({:grade_requires_type, %{name: "c", grade: :linear}}, &1)),
             "expected a {:grade_requires_type, …}, got #{inspect(errs)}"
    end

    test "an implicit graded binder with a missing type also names the grade" do
      errs = errors("mod G\n  fn f({@erased n :}) -> Int = 0\nend\n")

      assert Enum.any?(errs, &match?({:grade_requires_type, %{name: "n", grade: :erased}}, &1)),
             "expected a {:grade_requires_type, …}, got #{inspect(errs)}"
    end

    test "an unknown grade decorator names the offending spelling" do
      errs = errors("mod G\n  fn f(@bogus x : Int) -> Int = 0\nend\n")

      assert Enum.any?(errs, &match?({:unknown_grade, %{grade: "bogus"}}, &1)),
             "expected a {:unknown_grade, \"bogus\", …}, got #{inspect(errs)}"
    end

    test "an unknown grade owns its token, suggests a unique typo repair, and does not cascade" do
      src = "mod G\n  fn f(@liner x : Int) -> Int = x\nend\n"

      assert {:error, {:parse_error, [{:unknown_grade, details}]}} =
               Compiler.parse_source(src, file: "grade.cure")

      # The span covers the whole decorator, `@` included, so the repair edit can
      # replace it outright.
      assert details.span.start_line == 2
      assert details.span.start_column == 8
      assert details.span.end_line == 2
      assert details.span.end_column == 14

      {diagnostic, registry} = diagnostic(src)
      rendered = Renderer.plain(diagnostic, registry, width: 80)

      assert diagnostic.code == "E093"
      assert diagnostic.key == :unknown_grade

      assert rendered ==
               String.trim_trailing("""
               -- UNKNOWN RELEVANCE GRADE [E093] ----------------------------------- grade.cure

               `@liner` is not a relevance grade. Cure supports `@erased`, `@linear`,
               `@affine`.

               at grade.cure:2:8
               2 |   fn f(@liner x : Int) -> Int = x
                 |        ^^^^^^ this grade is not defined

               Hint: Replace it with `@linear`
               """)

      assert [suggestion] = diagnostic.suggestions
      assert suggestion.applicability == :machine_applicable
      expected_span = details.span
      assert [%{replacement: "@linear", span: ^expected_span}] = suggestion.edits

      lsp = Renderer.lsp(diagnostic, registry)

      assert lsp["range"] == %{
               "start" => %{"line" => 1, "character" => 7},
               "end" => %{"line" => 1, "character" => 13}
             }

      assert [edit] = lsp["data"]["suggestions"] |> hd() |> Map.fetch!("edits")
      assert edit["newText"] == "@linear"
      assert edit["range"] == lsp["range"]
    end

    test "a missing grade type points at the complete authored grade" do
      src = "mod G\n  fn f(@linear c :) -> Int = 0\nend\n"
      {diagnostic, registry} = diagnostic(src, "missing.cure")
      rendered = Renderer.plain(diagnostic, registry, width: 80)

      assert diagnostic.key == :grade_requires_type
      assert diagnostic.primary.span.start_line == 2
      assert diagnostic.primary.span.start_column == 8
      assert diagnostic.primary.span.end_column == 15

      assert rendered ==
               String.trim_trailing("""
               -- GRADED PARAMETER NEEDS A TYPE [E093] --------------------------- missing.cure

               The `@linear` grade on `c` controls how a value may be used, but no value type
               follows it.

               at missing.cure:2:8
               2 |   fn f(@linear c :) -> Int = 0
                 |        ^^^^^^^ add the parameter type after this grade

               Hint: Write `@linear c : TypeName`
               """)

      assert Renderer.lsp(diagnostic, registry)["range"] == %{
               "start" => %{"line" => 1, "character" => 7},
               "end" => %{"line" => 1, "character" => 14}
             }
    end

    test "@unrestricted is reported as an unknown grade (it has no spelling)" do
      errs = errors("mod G\n  fn f(@unrestricted x : Int) -> Int = 0\nend\n")

      assert Enum.any?(errs, &match?({:unknown_grade, %{grade: "unrestricted"}}, &1)),
             "expected a {:unknown_grade, \"unrestricted\", …}, got #{inspect(errs)}"
    end

    test "a well-formed grade still parses (no false positive)" do
      assert {:ok, _} = Compiler.parse_source("mod G\n  fn f(@linear c : Int) -> Int = c\nend\n")
    end
  end
end
