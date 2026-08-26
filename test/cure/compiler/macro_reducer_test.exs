defmodule Cure.Compiler.MacroReducerTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, MacroReducer}
  alias Cure.Core.{Context, Eval}
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.{Elaborator, Program}

  test "builds a complete constructor reducer and the elaborator accepts it" do
    assert {:ok, env} = Program.elaborate("mod M\n  type Flag = Off | On\n")

    scrutinee = {:variable, [scope: :local], "flag"}

    assert {:ok, ast} =
             MacroReducer.build_match(
               "Flag",
               scrutinee,
               [
                 %{constructor: :Off, body: {:literal, [subtype: :integer], 0}},
                 %{constructor: :On, body: {:literal, [subtype: :integer], 1}}
               ],
               env
             )

    flag_type = Eval.eval({:data, :"M#Flag", [], []}, Context.env(Context.empty(env)))
    ctx = Context.extend(Context.empty(env), flag_type)
    assert {:ok, _term, {:vdata, :"Std.Int#Int", []}} = Elaborator.elaborate_expr_typed(ast, ["flag"], ctx, env)
  end

  test "rejects incomplete, duplicate, unknown, and wrongly shaped constructor arms" do
    assert {:ok, env} = Program.elaborate("mod M\n  type Flag = Off | On\n")
    body = {:literal, [subtype: :integer], 0}

    assert {:error, {:incomplete_reducer, [:"M#On"]}} =
             MacroReducer.build_match("Flag", {:variable, [], "flag"}, [%{constructor: :Off, body: body}], env)

    assert {:error, :duplicate_reducer_constructor} =
             MacroReducer.build_match(
               "Flag",
               {:variable, [], "flag"},
               [%{constructor: :Off, body: body}, %{constructor: :Off, body: body}],
               env
             )

    assert {:error, {:unknown_reducer_constructor, [:Missing]}} =
             MacroReducer.build_match(
               "Flag",
               {:variable, [], "flag"},
               [%{constructor: :Off, body: body}, %{constructor: :Missing, body: body}],
               env
             )

    assert {:error, :invalid_reducer_arms} =
             MacroReducer.build_match("Flag", {:variable, [], "flag"}, :arms, env)

    assert {:error, :invalid_reducer_arm} =
             MacroReducer.build_match("Flag", {:variable, [], "flag"}, [42], env)
  end

  test "every reducer validation branch has stable user-facing output" do
    cases = [
      {:invalid_reducer_arms,
       """
       -- REDUCER ARMS ARE MALFORMED [E092] -------------------------------------------

       Reducer arms must be provided as a list with one arm for every constructor.

       Hint: Provide a list of constructor arms
       """},
      {:invalid_reducer_arm,
       """
       -- REDUCER ARM IS MALFORMED [E092] ---------------------------------------------

       Every reducer arm needs a constructor, an optional list of text bindings, and a
       body expression.

       Hint: Provide `constructor`, `bindings`, and `body` for this arm
       """},
      {:duplicate_reducer_constructor,
       """
       -- REDUCER CONSTRUCTOR IS REPEATED [E092] --------------------------------------

       Two reducer arms match the same constructor, so one arm can never be selected.

       Hint: Keep exactly one arm for each constructor
       """},
      {{:unknown_reducer_constructor, [:Missing]},
       """
       -- REDUCER USES AN UNKNOWN CONSTRUCTOR [E092] ----------------------------------

       The reducer refers to constructor `Missing`, which does not belong to the
       reflected data type.

       Hint: Use only constructors declared by the reduced data type
       """},
      {{:incomplete_reducer, [:On]},
       """
       -- REDUCER DOES NOT COVER EVERY CONSTRUCTOR [E092] -----------------------------

       The reducer has no arm for constructor `On`.

       Hint: Add one arm for every listed constructor
       """},
      {{:reducer_arity, :Pair, 1, 2},
       """
       -- REDUCER ARM HAS THE WRONG NUMBER OF BINDINGS [E092] -------------------------

       The `Pair` arm binds 1 values, but its constructor carries 2.

       Hint: Use exactly 2 bindings in this arm
       """}
    ]

    Enum.each(cases, fn {reason, expected} ->
      {diagnostic, registry} = Errors.to_diagnostic(reason, "reducer.cure", "")

      assert diagnostic.code == "E092"
      assert diagnostic.key == :macro_reducer_validation
      assert Renderer.plain(diagnostic, registry, width: 80) == String.trim_trailing(expected)

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["relatedInformation"] == []
    end)
  end

  test "view and flow dogfood share exhaustive reflection dispatch" do
    assert {:ok, env} = Program.elaborate("mod M\n  type Flag = Off | On\n")
    scrutinee = {:variable, [scope: :local], "flag"}
    body = {:literal, [subtype: :integer], 0}
    arms = [%{constructor: :Off, body: body}, %{constructor: :On, body: body}]

    assert {:ok, {:pattern_match, [generated_by: :macro_view], _}} =
             MacroReducer.build_view("Flag", scrutinee, arms, env)

    assert {:ok, flow_ast} = MacroReducer.build_flow("Flag", scrutinee, arms, env)
    assert {:pattern_match, [generated_by: :macro_flow], [^scrutinee | _]} = flow_ast

    flag_type = Eval.eval({:data, :"M#Flag", [], []}, Context.env(Context.empty(env)))
    ctx = Context.extend(Context.empty(env), flag_type)
    assert {:ok, _term, {:vdata, :"Std.Int#Int", []}} = Elaborator.elaborate_expr_typed(flow_ast, ["flag"], ctx, env)
  end

  test "declaration bundle integrates reducer, view, and flow outputs" do
    assert {:ok, env} = Program.elaborate("mod M\n  type Flag = Off | On\n")
    body = {:literal, [subtype: :integer], 0}
    arms = [%{constructor: :Off, body: body}, %{constructor: :On, body: body}]

    assert {:ok, %{kind: :macro_dispatch_bundle, reducer: reducer, view: view, flow: flow}} =
             MacroReducer.build_bundle("Flag", {:variable, [], "flag"}, arms, env)

    assert {:pattern_match, [generated_by: :macro_reducer], _} = reducer
    assert {:pattern_match, [generated_by: :macro_view], _} = view
    assert {:pattern_match, [generated_by: :macro_flow], _} = flow
  end
end
