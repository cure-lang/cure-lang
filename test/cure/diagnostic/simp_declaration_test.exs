defmodule Cure.Diagnostic.SimpDeclarationTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors
  alias Cure.Core.Env
  alias Cure.Diagnostic.{Adapter, Renderer, SimplificationProblem}
  alias Cure.Elab.{Program, SimpSet}

  test "an invalid simp declaration renders E112 at its authored name" do
    source = """
    mod InvalidSimpDiagnostic
      @simp
      fn looping(x: Int) -> Equivalent(Int, x, x) = missing_proof
    end
    """

    assert {:error, reason} = Program.elaborate(source)
    {diagnostic, registry} = Errors.to_diagnostic(reason, "simp.cure", source)
    rendered = Renderer.plain(diagnostic, registry, width: 120)

    assert diagnostic.code == "E112"

    assert %SimplificationProblem{
             kind: :inadmissible_rule,
             cause: {:simp_declaration, "looping", :non_decreasing_orientation}
           } =
             diagnostic.payload

    assert rendered =~ "The simp declaration `looping` is not admissible."
    assert rendered =~ "strictly more Core nodes"
    assert rendered =~ "equal-size and expanding rules can loop"
    assert rendered =~ "simp.cure:3:6"
    assert diagnostic.primary.span.start_line == 3
    assert diagnostic.primary.span.start_column == 6
  end

  test "span-free generated declarations still receive a structured diagnostic" do
    diagnostic = Adapter.from_error({:invalid_simp_lemma, "duplicate", :variable_duplication}, [])
    assert diagnostic.code == "E112"
    assert diagnostic.primary == nil
    assert inspect(diagnostic.body) =~ "substitution can invalidate the decrease"
  end

  test "simp recognition and validation ignore extra decorator metadata" do
    env = Env.empty()

    type =
      {:data, Cure.Core.Inductive.builtin(env, :eq), [{:int_type}],
       [
         {:app, {:global, :f}, {:var, 0}},
         {:var, 0}
       ]}

    for {name, args} <- [{:simp, []}, {:lemma, [{:literal, [], :simp}]}] do
      meta = [name: "decreasing", decorator: {:decorator, [line: 7, name: name, generated: true], args}]
      assert SimpSet.explicit?(meta)
      assert SimpSet.lemma?(meta)
      assert :ok = SimpSet.validate(meta, type, env)
    end
  end
end
