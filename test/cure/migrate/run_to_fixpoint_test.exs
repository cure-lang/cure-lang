# test/cure/migrate/run_to_fixpoint_test.exs
defmodule Cure.Migrate.RunToFixpointTest do
  use ExUnit.Case, async: true
  alias Cure.Migrate
  alias Cure.Migrate.Rule
  alias Cure.Compiler.{Lexer, Parser, Trivia}

  defp parse!(src) do
    {:ok, toks, trivia} = Lexer.tokenize(src, trivia: true)
    {:ok, ast} = Parser.parse(toks, emit_events: false)
    Trivia.attach(ast, trivia)
  end

  # Rule A: append marker :a. Rule B: append :b ONLY once :a is present.
  # A single-pass fold in [A, B] order handles this; but in [B, A] order B's
  # trigger is exposed only after A runs — proving the fixpoint re-scans.
  defp append_when(id, needle, mark) do
    %Rule{
      id: id,
      description: "t",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      warning_template: "m",
      detect_and_rewrite: fn {:block, m, ex}, _ctx ->
        has = Enum.any?(ex, &match?({:literal, _, ^needle}, &1))
        want = needle == nil or has
        already = Enum.any?(ex, &match?({:literal, _, ^mark}, &1))

        if want and not already,
          do: {:rewrite, {:block, m, ex ++ [{:literal, [subtype: :string], mark}]}},
          else: :no_change
      end
    }
  end

  test "a chained rewrite (B exposed only by A) converges via fixpoint even in B-before-A order" do
    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    rules = [append_when(:b, "a", "b"), append_when(:a, nil, "a")]
    {:ok, out, _warns} = Migrate.run_to_fixpoint(ast, rules: rules)
    {:block, _, ex} = out
    assert Enum.any?(ex, &match?({:literal, _, "a"}, &1))
    assert Enum.any?(ex, &match?({:literal, _, "b"}, &1))
  end

  test "a non-monotone rule set (A:x->y, B:y->x) hits max_passes and errors with the culprits" do
    flip = fn from, to, id ->
      %Rule{
        id: id,
        description: "t",
        phase: :syntactic,
        tier: :machine,
        since: "2026",
        warning_template: "m",
        detect_and_rewrite: fn {:block, m, ex}, _ctx ->
          if Enum.any?(ex, &match?({:literal, _, ^from}, &1)) do
            ex2 =
              Enum.map(ex, fn
                {:literal, meta, ^from} -> {:literal, meta, to}
                o -> o
              end)

            {:rewrite, {:block, m, ex2}}
          else
            :no_change
          end
        end
      }
    end

    ast = parse!("mod M\nfn f(x: Int) -> Int = 1\n")
    seed = {:block, elem(ast, 1), [{:literal, [subtype: :string], "x"}]}
    rules = [flip.("x", "y", :A), flip.("y", "x", :B)]

    assert {:error, {:no_convergence, culprits}} =
             Migrate.run_to_fixpoint(seed, rules: rules, max_passes: 4)

    assert :A in culprits or :B in culprits
  end

  test "a rule that drops a comment fails verify and aborts without further passes" do
    # Realistic rule-author bug: the rewrite rebuilds the node's meta from
    # scratch and forgets to carry its :leading trivia across (spec §5.2 names
    # Trivia.carry/2 for exactly this; a rule that skips it loses the comment).
    src = "mod M\n  ## a doc comment on f\n  fn f(x: Int) -> Int = 1\n"
    ast = parse!(src)

    # detect_and_rewrite receives the WHOLE-FILE ast (run/2 does not walk for
    # rules — each rule walks itself, per every other rule in this plan), so
    # this recurses to find the :function_def node and strips its :leading
    # trivia there, rather than pattern-matching the top-level node directly.
    drop_comment_rule = %Rule{
      id: :W_test_drops_comment,
      description: "t",
      phase: :syntactic,
      tier: :machine,
      since: "2026",
      warning_template: "m",
      detect_and_rewrite: fn ast, _ctx ->
        case strip_leading(ast, false) do
          {new_ast, true} -> {:rewrite, new_ast}
          {_ast, false} -> :no_change
        end
      end
    }

    assert {:error, {:verify_failed, :W_test_drops_comment}} =
             Migrate.run_to_fixpoint(ast, rules: [drop_comment_rule])
  end

  # Recurse to the first :function_def carrying :leading trivia and delete
  # that key; returns {new_ast, changed?}.
  defp strip_leading({:function_def, meta, body}, false) when is_list(meta) do
    if Keyword.has_key?(meta, :leading) do
      {{:function_def, Keyword.delete(meta, :leading), body}, true}
    else
      {{:function_def, meta, body}, false}
    end
  end

  defp strip_leading({k, meta, ch}, changed?) when is_list(ch) do
    {new_ch, changed?} = strip_leading(ch, changed?)
    {{k, meta, new_ch}, changed?}
  end

  defp strip_leading(l, changed?) when is_list(l) do
    Enum.map_reduce(l, changed?, fn node, acc ->
      if acc, do: {node, acc}, else: strip_leading(node, acc)
    end)
  end

  defp strip_leading(other, changed?), do: {other, changed?}
end
