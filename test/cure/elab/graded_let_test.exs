defmodule Cure.Elab.GradedLetTest do
  @moduledoc """
  Slice 5b: QTT grades on `let`.

      let @linear c = mk()            -- rhs infers: no ascription needed
      let @linear c : Chan(Cmd) = e     -- rhs is check-only: ascription REQUIRED

  Idris's `letBinder` is `multiplicity >> pat >> option (":" type) >> "=" >> val`
  (`Idris/Parser.idr:821-824`), so the type stays **optional even when graded**. The
  grade and the type are orthogonal: `let_inferred/8` synthesises the rhs's type and
  hands it to `bind_once_let/9`, which builds the `:let` node. Nothing about a grade
  forces an annotation.

  ## The one place a graded `let` MUST be ascribed, and why

  When the rhs has no inferable type — a bare lambda, an `if`, a `pickup` —
  `let_inferred/8` abandons the `:let` node entirely and **surface-substitutes** the
  rhs into its single use site. On that path no `:let` node is ever built, so there is
  nowhere to put the grade and it would be **silently dropped**: the program would
  compile, pass, and lie about its linearity.

  So the rule is mechanical, not aesthetic: *a graded `let` must produce a real `:let`
  node.* If the rhs infers, that is automatic. If it does not, require the ascription
  and say so — never substitute and discard the grade.

  The grade only attaches to a **simple variable binder**. A destructuring `let`
  lowers to a `case`, whose branch binders take their grades from the constructor's
  field quantities; there is no single Core binder for the grade to land on. That is a
  parse error, not a silently-ignored annotation.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler
  alias Cure.Core.{Env, Validator}
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program

  # `mk/0` is inferable; `sink/1` consumes linearly; `use2/2` consumes at omega.
  @preamble "mod L\n" <>
              "  fn mk() -> Int = 1\n" <>
              "  fn sink(@linear x : Int) -> Int = x\n" <>
              "  fn use2(a: Int, b: Int) -> Int = a\n"

  defp elab(body),
    do: Program.semantic_result(Program.elaborate(@preamble <> "  fn f() -> Int =\n" <> body <> "end\n"))

  defp lets(env, name) do
    env
    |> Env.get_def(name)
    |> Map.fetch!(:body)
    |> Validator.nodes()
    |> Enum.filter(&match?({:let, _, _, _, _}, &1))
  end

  # Every `{:assignment, meta, _}` in a parsed module, in source order.
  defp assignment_metas(src) do
    {:ok, ast} = Compiler.parse_source(src)
    collect(ast)
  end

  defp collect({:assignment, meta, children}), do: [meta | Enum.flat_map(children, &collect/1)]
  defp collect({_t, _m, children}) when is_list(children), do: Enum.flat_map(children, &collect/1)
  defp collect(list) when is_list(list), do: Enum.flat_map(list, &collect/1)
  defp collect(_), do: []

  defp let_grade(src) do
    src |> assignment_metas() |> List.first() |> Keyword.get(:grade)
  end

  describe "the parser records a grade on a let binder" do
    test "a graded let needs no type when the rhs will infer" do
      meta =
        assignment_metas(@preamble <> "  fn f() -> Int =\n    let @linear c = mk()\n    c\nend\n") |> List.first()

      assert Keyword.get(meta, :grade) == :linear
      refute Keyword.has_key?(meta, :type_annotation)
    end

    test "a graded let may write the `:` and still leave the type to inference" do
      # `let @linear c : = mk()` states an annotation and then omits it. The binder
      # is still well formed, so the parser consumes the `:` and stops at the `=`
      # rather than handing `=` to the type parser, which would read past the
      # binding and report whatever followed it instead.
      meta =
        assignment_metas(@preamble <> "  fn f() -> Int =\n    let @linear c : = mk()\n    c\nend\n")
        |> List.first()

      assert Keyword.get(meta, :grade) == :linear
      refute Keyword.has_key?(meta, :type_annotation)
    end

    test "a graded let may carry a type as well" do
      meta =
        assignment_metas(@preamble <> "  fn f() -> Int =\n    let @linear c : Int = mk()\n    c\nend\n") |> List.first()

      assert Keyword.get(meta, :grade) == :linear
      assert Keyword.has_key?(meta, :type_annotation)
    end

    test "affine and erased are spellable too" do
      assert :affine = let_grade(@preamble <> "  fn f() -> Int =\n    let @affine c = mk()\n    0\nend\n")
      assert :erased = let_grade(@preamble <> "  fn f() -> Int =\n    let @erased c = mk()\n    0\nend\n")
    end

    test "an ungraded let records no grade — absent means omega" do
      assert nil == let_grade(@preamble <> "  fn f() -> Int =\n    let c = mk()\n    c\nend\n")
    end
  end

  describe "there is exactly ONE spelling, and it binds a variable" do
    test "@unrestricted is not a spelling on a let either" do
      assert {:error, _} =
               Compiler.parse_source(@preamble <> "  fn f() -> Int =\n    let @unrestricted c = mk()\n    c\nend\n")
    end

    test "an unknown grade decorator is a parse error" do
      assert {:error, _} =
               Compiler.parse_source(@preamble <> "  fn f() -> Int =\n    let @bogus c = mk()\n    c\nend\n")
    end

    test "a graded DESTRUCTURING let is a parse error, not a dropped annotation" do
      # A destructuring `let` becomes a `case`; its binders take their grades from the
      # constructor's field quantities, so there is no binder for this grade.
      src = "mod L\n  fn f(xs: List(Int)) -> Int =\n    let @linear [h | _t] = xs\n    h\nend\n"
      assert {:error, _} = Compiler.parse_source(src)
    end

    test "a graded destructuring let labels the pattern and its grade" do
      src = "mod L\n  fn f(xs: List(Int)) -> Int =\n    let @linear [h | _t] = xs\n    h\nend\n"

      assert {:error, {:parse_error, [{:graded_let_requires_variable, details}]}} =
               Compiler.parse_source(src, file: "graded_let.cure")

      {diagnostic, registry} =
        Cure.Compiler.Errors.to_diagnostic(
          {:parse_error, [{:graded_let_requires_variable, details}]},
          "graded_let.cure",
          src
        )

      rendered = Renderer.plain(diagnostic, registry, width: 80)

      assert diagnostic.code == "E093"
      assert diagnostic.key == :graded_let_requires_variable
      # The grade is a prefix decorator, so `@linear` comes first and the offending
      # pattern sits after it. The caret belongs on the pattern -- that is what has
      # to change -- with the grade carried as a related label.
      assert diagnostic.primary.span.start_line == 3
      assert diagnostic.primary.span.start_column == 17
      assert diagnostic.primary.span.end_column == 25

      assert rendered ==
               String.trim_trailing("""
               -- GRADED BINDING NEEDS A VARIABLE [E093] ---------------------- graded_let.cure

               A `linear` grade controls one Core binder, but this pattern introduces multiple
               or destructured bindings.

               at graded_let.cure:3:17
               3 |     let @linear [h | _t] = xs
                 |         ------- ^^^^^^^^ this grade applies to the binding; this pattern is not a single variable binding

               Hint: Bind the value to one graded variable, then destructure it in a separate `let`
               """)

      lsp = Renderer.lsp(diagnostic, registry)

      assert lsp["range"] == %{
               "start" => %{"line" => 2, "character" => 16},
               "end" => %{"line" => 2, "character" => 24}
             }

      assert [%{"location" => %{"range" => grade_range}, "message" => message}] =
               lsp["relatedInformation"]

      assert grade_range == %{
               "start" => %{"line" => 2, "character" => 8},
               "end" => %{"line" => 2, "character" => 15}
             }

      assert message == "this grade applies to the binding"
    end

    test "an ungraded destructuring let still parses" do
      src = "mod L\n  fn f(xs: List(Int)) -> Int =\n    let [h | _t] = xs\n    h\nend\n"
      assert {:ok, _} = Compiler.parse_source(src)
    end
  end

  describe "the grade reaches the Core :let binder" do
    test "a linear let builds {:let, :linear, …}" do
      assert {:ok, env} = elab("    let @linear c = mk()\n    sink(c)\n")
      assert [{:let, :linear, _ty, _val, _body}] = lets(env, :f)
    end

    test "an ungraded let still builds {:let, :unrestricted, …}" do
      assert {:ok, env} = elab("    let c = mk()\n    use2(c, c)\n")
      assert [{:let, :unrestricted, _, _, _}] = lets(env, :f)
    end
  end

  describe "the usage check enforces a let's declared grade" do
    test "a linear let consumed exactly once by a linear position is accepted" do
      assert {:ok, _} = elab("    let @linear c = mk()\n    sink(c)\n")
    end

    test "a linear let used zero times is REJECTED" do
      assert {:error, {:usage_violation, %{kind: :let, declared: :linear, used: :erased}}} =
               elab("    let @linear c = mk()\n    0\n")
    end

    test "a linear let used twice is REJECTED" do
      assert {:error, {:usage_violation, %{kind: :let, declared: :linear, used: :unrestricted}}} =
               elab("    let @linear c = mk()\n    use2(c, c)\n")
    end

    test "a linear let handed to an omega position is REJECTED" do
      assert {:error, {:usage_violation, %{kind: :let, declared: :linear, used: :unrestricted}}} =
               elab("    let @linear c = mk()\n    use2(c, 0)\n")
    end

    test "an affine let used zero times is ACCEPTED" do
      assert {:ok, _} = elab("    let @affine c = mk()\n    0\n")
    end
  end

  describe "an erased let binder has no runtime value" do
    # `Relevance` runs two mechanisms (see its moduledoc). The counting check covers
    # `:linear`/`:affine`; `:erased` belongs to the POSITION check, whose tracked set
    # held only erased parameters and erased constructor FIELDS. `:let` binders were
    # never added to it, so before 5b made `:erased` spellable on a `let`, nothing
    # could write this program — and once it could, the annotation was unenforced.
    # `Emit` lowers every `:let` to an unconditional bind, so the value does exist at
    # runtime; the lie is in the annotation, not in erasure.
    test "returning an erased let binder is REJECTED" do
      assert {:error, {:erased_used_relevantly, %{site: :returned}}} =
               elab("    let @erased c = mk()\n    c\n")
    end

    test "passing an erased let binder in a present position is REJECTED" do
      assert {:error, {:erased_used_relevantly, %{site: :present_arg}}} =
               elab("    let @erased c = mk()\n    use2(c, 0)\n")
    end

    test "an unused erased let binder is fine" do
      assert {:ok, _} = elab("    let @erased c = mk()\n    0\n")
    end

    test "an erased LAMBDA binder is policed the same way" do
      # Not yet spellable at the surface (lambda grades are a follow-up), so this
      # drives `Relevance.check/4` on the Core term directly.
      nat = {:data, :Nat, [], []}
      body = {:lam, :erased, nat, {:var, 0}}

      assert {:error, {:erased_used_relevantly, %{site: :returned}}} =
               Cure.Elab.Relevance.check(Env.empty(), :f, [], body)
    end

    test "an unrestricted lambda binder is not policed" do
      nat = {:data, :Nat, [], []}
      assert :ok = Cure.Elab.Relevance.check(Env.empty(), :f, [], {:lam, :unrestricted, nat, {:var, 0}})
    end
  end

  describe "a graded let must produce a real :let node — never a dropped grade" do
    # `fn(x) -> x + 1` is check-only: `let_inferred/8` cannot synthesise its type and
    # falls back to surface substitution, which builds no `:let` node at all.
    @lam "fn(x) -> x + 1"

    test "a graded let with a non-inferable rhs is REJECTED, not silently substituted" do
      src =
        "mod L\n" <>
          "  fn ap(@linear g : (Int) -> Int, n: Int) -> Int = g(n)\n" <>
          "  fn f(n: Int) -> Int =\n    let @linear h = #{@lam}\n    ap(h, n)\nend\n"

      assert {:error, {:source_context, {:graded_let_needs_annotation, %{name: "h"}}, _}} =
               Program.elaborate(src)
    end

    test "ascribing it makes the same program work, with the grade preserved" do
      src =
        "mod L\n" <>
          "  fn ap(@linear g : (Int) -> Int, n: Int) -> Int = g(n)\n" <>
          "  fn f(n: Int) -> Int =\n    let @linear h : (Int) -> Int = #{@lam}\n    ap(h, n)\nend\n"

      assert {:ok, env} = Program.elaborate(src)
      assert [{:let, :linear, _, _, _}] = lets(env, :f)
    end

    test "an UNGRADED let with a non-inferable rhs keeps today's substitution path" do
      # Regression: omega imposes no obligation, so nothing about this program moves.
      src =
        "mod L\n" <>
          "  fn ap(g: (Int) -> Int, n: Int) -> Int = g(n)\n" <>
          "  fn f(n: Int) -> Int =\n    let h = #{@lam}\n    ap(h, n)\nend\n"

      assert {:ok, _} = Program.elaborate(src)
    end

    test "an ungraded non-inferable rhs used twice still reports the ungraded error" do
      src =
        "mod L\n" <>
          "  fn ap(g: (Int) -> Int, n: Int) -> Int = g(n)\n" <>
          "  fn f(n: Int) -> Int =\n    let h = #{@lam}\n    ap(h, n) + ap(h, n)\nend\n"

      assert {:error, {:source_context, {:let_needs_annotation, %{name: "h"}}, _}} = Program.elaborate(src)
    end
  end
end
