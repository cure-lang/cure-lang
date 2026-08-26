defmodule Cure.Compiler.TopLevelAfterMacroBlockTest do
  use ExUnit.Case, async: false
  @moduletag timeout: 180_000

  alias Cure.Compiler.{Lexer, Parser}

  # A macro family body (`fsm`, `actor`, `sup`, ...) captures its tokens up to
  # -- but not including -- the `dedent` that closes it, on the convention that a
  # structural delimiter belongs to the enclosing parser. `parse_block_body/3`
  # honours that convention by skipping any dedent deeper than its own indent,
  # which is why a `mod` body kept parsing past an `fsm`.
  #
  # The top-level statement loop had no such clause: it treated the leftover
  # dedent as end-of-program and silently discarded every declaration after the
  # first macro block. No error was raised -- the code was simply gone.

  defp top_level_nodes(source) do
    {:ok, tokens} = Lexer.tokenize(source)
    {:ok, ast} = Parser.parse(tokens, prelude_providers: [])
    {:ok, ast} = Cure.Elab.Program.expand_declaration_uses(ast)

    case ast do
      {:block, _meta, items} -> items
      single -> [single]
    end
  end

  defp names(nodes) do
    Enum.map(nodes, fn {tag, meta, _children} ->
      {tag, is_list(meta) && (Keyword.get(meta, :name) || Keyword.get(meta, :module))}
    end)
  end

  describe "declarations following a top-level macro block" do
    test "a function after a structured fsm survives parsing" do
      nodes =
        top_level_nodes("""
        use Std.Fsm

        fsm AfterStructured
          state Int
          events
            Tick -> :keep_state_and_data

        fn plain() -> Int = 7
        """)

      assert {:function_def, "plain"} in names(nodes)
    end

    test "a function after a transition-table fsm survives parsing" do
      nodes =
        top_level_nodes("""
        use Std.Fsm

        fsm AfterTable with Int
          Locked   --Coin--> Unlocked
          Unlocked --Push--> Locked

        fn plain() -> Int = 7
        """)

      assert {:function_def, "plain"} in names(nodes)
    end

    test "a second fsm in the same unit survives parsing" do
      nodes =
        top_level_nodes("""
        use Std.Fsm

        fsm FirstMachine
          state Int
          events
            Tick -> :keep_state_and_data

        fsm SecondMachine
          state Int
          events
            Tock -> :keep_state_and_data
        """)

      assert {:lift_module, :"Cure.Main.FirstMachine"} in names(nodes)
      assert {:lift_module, :"Cure.Main.SecondMachine"} in names(nodes)
    end

    test "a mod after a top-level fsm survives parsing" do
      nodes =
        top_level_nodes("""
        use Std.Fsm

        fsm BeforeMod
          state Int
          events
            Tick -> :keep_state_and_data

        mod Later
          fn plain() -> Int = 7
        """)

      assert {:container, "Later"} in names(nodes)
    end
  end

  describe "the dropped declarations are actually compiled" do
    test "a function declared after an fsm is emitted and callable" do
      source = """
      use Std.Fsm

      fsm EmittedNeighbour
        state Int
        events
          Tick -> :keep_state_and_data

      fn neighbour_value() -> Int = 42
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(source, emit_events: false)
      assert {:neighbour_value, 0} in :"Cure.Main".module_info(:exports)
      assert apply(:"Cure.Main", :neighbour_value, []) == 42
    end

    # The dropped declarations were never elaborated, so nothing in them was
    # ever checked. A type error after an fsm compiled clean.
    test "a type error after an fsm is still reported" do
      source = """
      use Std.Fsm

      fsm UncheckedNeighbour
        state Int
        events
          Tick -> :keep_state_and_data

      fn bad() -> Int = no_such_function_at_all()
      """

      assert {:error, _} = Cure.Compiler.compile_and_load(source, emit_events: false)
    end

    test "both fsms in a unit are emitted" do
      source = """
      use Std.Fsm

      fsm EmittedFirst
        state Int
        events
          Tick -> :keep_state_and_data

      fsm EmittedSecond
        state Int
        events
          Tock -> :keep_state_and_data
      """

      assert {:ok, _} = Cure.Compiler.compile_and_load(source, emit_events: false)
      assert apply(:"Cure.Main.EmittedFirst", :init, [0]) == {:ok, :initial, 0}
      assert apply(:"Cure.Main.EmittedSecond", :init, [0]) == {:ok, :initial, 0}
    end
  end
end
