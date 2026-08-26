defmodule Cure.Elab.MacroContextReflectionTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.MacroExpand
  alias Cure.Elab.Program

  # A Tier-3 elab that branches on the reflected expansion context: inside a
  # callback it sees a `callback_context` node, at an ordinary use-site it sees
  # nothing. The pinned example is the no-context expansion.
  @record_source """
  mod M
    use Std.Syntax

    macro Mk
      syntax mk <x: Code> computed by build_it
        example mk 1 expands 0
      explain
        Code =>
          "expects code"
        keyword "mk" =>
          "starts with mk"

    fn build_it(input: MkSyntax) -> Syntax = match input.context
      Node(_, _, _) -> Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(1))
      _ -> Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(0))
  """

  @generic_source """
  mod M
    use Std.Syntax

    macro Gen
      syntax gen <x: Code> contextual computed by build_gen

    fn build_gen(input: Syntax) -> Syntax = input
  """

  defp use_site(keyword, elab) do
    {:computed_use,
     [keyword: keyword, syntax_type: String.capitalize(keyword) <> "Syntax", syntax_fields: ["x"], line: 1, col: 1],
     [
       {:variable, [scope: :local], elab},
       {:macro_input, [keyword: keyword], [{:literal, [subtype: :integer], 7}]}
     ]}
  end

  @context %{
    behaviour: :gen_server,
    callback: :handle_cast,
    arity: 2,
    parameter_names: ["msg", "state"],
    return_annotation: :declared
  }

  test "a computed elab reads the callback context from its derived record" do
    assert {:ok, env} = Program.elaborate(@record_source)

    assert {:ok, {:literal, [subtype: :integer], 1}} =
             MacroExpand.expand(use_site("mk", "build_it"), env, callback_context: @context)
  end

  test "a computed elab outside a callback sees no context in its derived record" do
    assert {:ok, env} = Program.elaborate(@record_source)

    assert {:ok, {:literal, [subtype: :integer], 0}} =
             MacroExpand.expand(use_site("mk", "build_it"), env)
  end

  test "the generic syntax input carries the callback context as an attribute" do
    assert {:ok, env} = Program.elaborate(@generic_source)

    assert {:ok, {:macro_input, meta, _children}} =
             MacroExpand.expand(use_site("gen", "build_gen"), env, callback_context: @context)

    assert {:callback_context, attrs, []} = meta[:expansion_context]
    assert attrs[:behaviour] == :gen_server
    assert attrs[:callback] == :handle_cast
    assert attrs[:arity] == 2
    assert attrs[:parameter_names] == ["msg", "state"]
    assert attrs[:return_annotation] == :declared
  end

  test "a computed rule may not claim the reserved context field for a hole" do
    source = """
    mod M
      use Std.Syntax

      macro Mk
        syntax mk <context: Code> contextual computed by build_it

      fn build_it(input: MkSyntax) -> Syntax = input.context
    """

    assert {:error,
            {:source_context, {:reserved_syntax_field, "context", ["mk"]},
             %{span: %Cure.Diagnostic.Span{start_line: 5, start_column: 15}}}} = Program.elaborate(source)
  end

  test "the generic syntax input carries no context attribute outside a callback" do
    assert {:ok, env} = Program.elaborate(@generic_source)

    assert {:ok, {:macro_input, meta, _children}} = MacroExpand.expand(use_site("gen", "build_gen"), env)
    refute Keyword.has_key?(meta, :expansion_context)
  end
end
