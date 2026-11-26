defmodule Cure.Compiler.TacticMacroAuditTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser, Printer}
  alias Cure.Core.{Env, Kernel}
  alias Cure.Elab.Program

  defp parse!(source) do
    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp checked!(source) do
    assert {:ok, env} = Program.elaborate(source)
    assert :ok = Kernel.check_def(env, Env.resolve_key(env, env.defs, :theorem))
    env
  end

  test "printing retains tactic declarations and captured invocations" do
    source = """
    mod PrintedTactics
      macro Tactics
        tactic close becomes simplify
        tactic finish <e: Code> becomes exact e
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because finish reflexive(x)
    end
    """

    printed = source |> parse!() |> Printer.quoted_to_string()
    assert printed =~ "tactic close becomes simplify"
    assert printed =~ "tactic finish <e: Code> becomes exact e"
    assert printed =~ "because finish reflexive(x)"
    checked!(printed)
    assert printed |> parse!() |> Printer.quoted_to_string() == printed
  end

  test "printing round-trips rewrite-all tactic sequences" do
    source = """
    mod PrintedSequence
      macro Tactics
        tactic move <e: Code> becomes
          rewrite using e all
          simplify
      type Pair = Pair(Int, Int)
      fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Pair, Pair(x, x), Pair(y, y)) = proof chain
        Pair(x, x) == Pair(y, y)
        because move h
    end
    """

    printed = source |> parse!() |> Printer.quoted_to_string()
    assert printed =~ "rewrite using e all"
    checked!(printed)
    assert printed |> parse!() |> Printer.quoted_to_string() == printed
  end

  test "a tactic keyword stays an ordinary function in nested evidence operands" do
    checked!("""
    mod NestedEvidenceCall
      macro Tactics
        tactic finish <e: Code> becomes exact e
      fn finish(x: Int) -> Int = x
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because exact reflexive(finish(x))
    end
    """)
  end

  test "a structured token after a literal-led tactic is a diagnostic, not a parser crash" do
    source = ~S"""
    mod StructuredTacticMismatch
      macro Tactics
        tactic finish with <e: Code> becomes exact e
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because finish "value #{x}"
    end
    """

    assert {:error, _} = Program.elaborate(source)
  end

  test "example expected expressions parse in their own tactic context" do
    checked!("""
    mod ContextualTacticPin
      macro Tactics
        tactic finish <e: Code> becomes exact e
          example finish h expands exact h
        explain
          keyword "finish" => "finish with the supplied proof"
          Code => "a proof expression"
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because finish reflexive(x)
    end
    """)
  end

  test "a tactic in a hybrid macro does not change ordinary syntax pins" do
    checked!("""
    mod HybridTacticPin
      fn exact(x: Int) -> Int = x
      macro Tactics
        tactic close becomes simplify
        syntax keep <e: Code> becomes e
          example keep exact(1) expands exact(1)
      fn via_syntax(x: Int) -> Int = keep exact(x)
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because close
    end
    """)
  end

  test "multi-command templates support explained block example pins and printing" do
    source = """
    mod SequenceTacticPin
      macro Tactics
        tactic move <e: Code> becomes
          rewrite using e all
          simplify
          example move h expands
            rewrite using h all
            simplify
        explain
          keyword "move" => "rewrite and simplify"
          Code => "an equality proof"
      type Pair = Pair(Int, Int)
      fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Pair, Pair(x, x), Pair(y, y)) = proof chain
        Pair(x, x) == Pair(y, y)
        because move h
    end
    """

    checked!(source)
    printed = source |> parse!() |> Printer.quoted_to_string()
    checked!(printed)
    assert printed |> parse!() |> Printer.quoted_to_string() == printed
  end

  test "tactic declaration keywords cannot silently override built-in commands" do
    for name <- ["exact", "fn", "have"] do
      assert {:error, {:source_context, {:invalid_tactic_expansion, ^name, :reserved_tactic_keyword}, _}} =
               Program.elaborate("""
               mod ReservedTactic
                 macro Tactics
                   tactic #{name} becomes simplify
                 fn theorem(x: Int) -> Equivalent(Int, x, x) = reflexive(x)
               end
               """)
    end
  end

  test "unsupported capture kinds are refused even on unused tactic rules" do
    assert {:error, {:source_context, {:unsupported_hole_type, "Bogus"}, _}} =
             Program.elaborate("""
             mod UnsupportedTacticCapture
               macro Tactics
                 tactic finish <e: Bogus> becomes exact e
               fn theorem(x: Int) -> Equivalent(Int, x, x) = reflexive(x)
             end
             """)
  end

  test "printing preserves present and absent optional literals and whitespace repetitions" do
    for {rule, invocation} <- [
          {"tactic close (now)? becomes simplify", "close now"},
          {"tactic close (now)? becomes simplify", "close"},
          {"tactic close now ... becomes simplify", "close now now"},
          {"tactic close <e: Code> ... becomes simplify", "close 1 2"}
        ] do
      source = """
      mod PrintedTacticGrammar
        macro Tactics
          #{rule}
        fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
          x == x
          because #{invocation}
      end
      """

      checked!(source)
      printed = source |> parse!() |> Printer.quoted_to_string()
      assert printed =~ "because #{invocation}"
      checked!(printed)
      assert printed |> parse!() |> Printer.quoted_to_string() == printed
    end
  end

  @tag :tmp_dir
  test "source-imported tactics retain their provider's helper grammar despite caller shadowing", %{tmp_dir: dir} do
    helper = Path.join(dir, "helper.cure")
    provider = Path.join(dir, "provider.cure")
    consumer = Path.join(dir, "consumer.cure")
    File.write!(helper, "mod Audit.Helper\n  macro Rules\n    tactic private_close becomes simplify\n")

    File.write!(
      provider,
      "mod Audit.Provider\n  use Audit.Helper\n  macro Rules\n    tactic outer becomes private_close\n"
    )

    File.write!(consumer, """
    mod Audit.Consumer
      use Audit.Provider
      macro Rules
        tactic private_close becomes exact missing_proof
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because outer
    """)

    assert {:ok, checked} =
             Cure.Compiler.ModulePipeline.check([consumer, provider, helper], package: "audit", source_roots: [dir])

    env = Map.fetch!(checked.body_envs, {"audit", "Audit.Consumer"})
    assert :ok = Kernel.check_def(env, :"Audit.Consumer#theorem")
  end

  test "nested alias expansion pins compare commands, not internal wrappers" do
    for expected <- ["finish h", "exact h"] do
      checked!("""
      mod NestedAliasPin
        macro Tactics
          tactic finish <e: Code> becomes exact e
          tactic close <e: Code> becomes finish e
            example close h expands #{expected}
        fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
          x == x
          because close reflexive(x)
      end
      """)
    end
  end

  test "type-only tactic pins execute against their stated goal and refuse a false one" do
    source = """
    mod TypedTacticPin
      macro Tactics
        tactic close becomes simplify
          example close expands : Equivalent(Int, 0, 0)
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because close
    end
    """

    checked!(source)

    assert {:error, {:example_type_mismatch, [_]}} =
             source
             |> String.replace("Equivalent(Int, 0, 0)", "Equivalent(Int, 0, 1)")
             |> Program.elaborate()
             |> Program.semantic_result()
  end

  test "tactic invocation source locations do not change its semantic identity" do
    source = """
    mod TacticMetadata
      macro Tactics
        tactic finish <e: Code> becomes exact e
      fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
        x == x
        because finish reflexive(x)
    end
    """

    [before] = source |> parse!() |> tactic_uses()
    [after_blank] = ("\n" <> source) |> parse!() |> tactic_uses()
    assert Cure.MetaAST.Metadata.semantic_equal?(before, after_blank)
  end

  defp tactic_uses({:tactic_script, _, _} = node), do: [node]
  defp tactic_uses({_tag, _meta, children}) when is_list(children), do: Enum.flat_map(children, &tactic_uses/1)
  defp tactic_uses(list) when is_list(list), do: Enum.flat_map(list, &tactic_uses/1)
  defp tactic_uses(_other), do: []
end
