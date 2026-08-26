defmodule Cure.Compiler.SyntaxBuilderTest do
  use ExUnit.Case, async: false

  @source """
  mod M
    use Std.Syntax

    fn tag_of() -> Atom = tag(Node(:sample, [], []))

    fn quoted_children() -> List(Syntax) =
      children(Quoted(Leaf(:literal, [], SInt(1))))

    fn find_name() -> AttrResult =
      attr([KV(:other, SInt(0)), KV(:name, SStr("worker"))], :name)

    fn context_name() -> AttrResult =
      context_attr(
        Node(:sample, [attr_value(:expansion_context, SSyntax(Node(:callback_context, [KV(:callback, SAtom(:handle_cast))], [])))], []),
        :callback
      )

    fn build_node() -> Syntax =
      node(:generated, [attr_value(:kind, syntax_atom(:actor))], [])

    fn build_literals() -> List(Syntax) = [int_literal(7), float_literal(2.5), bool_literal(true), string_literal("ok"), atom_literal(:ready)]

    fn build_unit() -> Syntax = unit_literal()

    fn build_function() -> Syntax =
      function_from(FunctionSpec{
        name: "handle",
        parameters: [linear_parameter_spec("from", variable("Reply"))],
        returns: variable("Result"),
        body: variable("from")
      })

    fn build_alias() -> Syntax = alias_from(alias_spec("State", variable("Int")))

    fn build_module() -> Syntax =
      module_from(ModuleSpec{
        name: "Cure.Generated.Worker",
        behaviour: :gen_server,
        declarations: []
      })

    fn build_arm() -> Syntax = match_arm(variable("Ready"), atom_literal(:ok))

    fn build_name_intents() -> List(Syntax) =
      [caller_identifier("state"), private_identifier("temporary"), exported_identifier("start_link")]
  """

  test "source-level syntax helpers analyze and construct reflected syntax" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)

    assert apply(module, :tag_of, []) == :sample

    assert apply(module, :quoted_children, []) == [
             {:Leaf, :literal, [], {:SInt, 1}}
           ]

    assert apply(module, :find_name, []) == {:Found, {:SStr, {:String, String.to_charlist("worker")}}}

    assert apply(module, :context_name, []) == {:Found, {:SAtom, :handle_cast}}

    assert apply(module, :build_node, []) ==
             {:Node, :generated, [{:KV, :kind, {:SAtom, :actor}}], []}

    assert apply(module, :build_literals, []) == [
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :integer}}], {:SInt, 7}},
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :float}}], {:SFloat, 2.5}},
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :boolean}}], {:SBool, true}},
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :string}}], {:SStr, {:String, ~c"ok"}}},
             {:Leaf, :literal, [{:KV, :subtype, {:SAtom, :symbol}}], {:SAtom, :ready}}
           ]

    assert apply(module, :build_unit, []) == {:Node, :unit_value, [], []}

    assert {:Node, :function_def, attrs, [body]} = apply(module, :build_function, [])
    assert {:KV, :name, {:SStr, {:String, ~c"handle"}}} in attrs
    assert Enum.any?(attrs, &match?({:KV, :return_type, {:SSyntax, _}}, &1))
    assert {:Leaf, :variable, _, {:SStr, {:String, ~c"from"}}} = body

    # `typealias` is load-bearing, not decoration: the elaborator's header
    # pre-pass only gives a flagged alias a forward-referenceable header, and
    # module lifting inlines the enclosing unit's declarations *ahead* of the
    # generated ones -- so an unflagged alias is invisible to them.
    assert {:Node, :type_annotation, alias_attrs, [_]} = apply(module, :build_alias, [])
    assert {:KV, :name, {:SStr, {:String, ~c"State"}}} in alias_attrs
    assert {:KV, :typealias, {:SBool, true}} in alias_attrs

    assert {:Node, :lift_module, attrs, []} = apply(module, :build_module, [])
    assert {:KV, :module, {:SStr, {:String, ~c"Cure.Generated.Worker"}}} in attrs
    assert {:KV, :behaviour, {:SAtom, :gen_server}} in attrs

    assert {:Node, :match_arm, [{:KV, :pattern, {:SSyntax, _}}], [_]} =
             apply(module, :build_arm, [])

    assert [
             {:Leaf, :variable, [{:KV, :scope, {:SAtom, :caller}}], {:SStr, {:String, ~c"state"}}},
             {:Leaf, :fresh_name, [], {:SStr, {:String, ~c"temporary"}}},
             {:Leaf, :variable, [{:KV, :scope, {:SAtom, :exported}}], {:SStr, {:String, ~c"start_link"}}}
           ] = apply(module, :build_name_intents, [])
  end

  test "raw syntax construction is available only through an explicit unsafe API" do
    source = """
    mod M
      use Std.Syntax
      use Std.Syntax.Raw

      fn build_raw() -> Syntax = unsafe_node(:raw, [], [unsafe_leaf(:value, [], SInt(1))])
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :build_raw, []) ==
             {:Node, :raw, [], [{:Leaf, :value, [], {:SInt, 1}}]}
  end
end
