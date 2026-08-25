defmodule Cure.Compiler.DeclarationMacroExpansionTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.Errors
  alias Cure.Diagnostic.Renderer
  alias Cure.Elab.Program
  alias Cure.MetaAST.Metadata

  defp source_slice(source, span),
    do: binary_part(source, span.start_byte, span.end_byte - span.start_byte)

  @source """
  mod M
    use Std.Syntax

    macro Make
      syntax make <x: Code> computed by id

    fn id(input: MakeSyntax) -> Syntax = input.x

    make lift module Cure.DeclarationMacroActor
      behaviour gen_server
      callback init(initial: Int) returns Effect(Tuple(Atom, Int)) = %[:ok, initial]
  end
  """

  test "a computed declaration expands before lifted modules are collected" do
    assert {:ok, module} = Cure.Compiler.compile_and_load(@source, emit_events: false)
    assert module == :"Cure.M"
    assert apply(:"Cure.DeclarationMacroActor", :init, [7]) == {:ok, 7}
  end

  test "a generated module and each declaration retain the authored macro provenance" do
    assert {:ok, ast} = Cure.Compiler.parse_source(@source, file: "generated.cure")
    assert {:ok, expanded} = Program.expand_declaration_uses(ast)
    assert {:lift_module, meta, []} = find_lift_module(expanded)

    assert meta[:source_provenance] == %{file: "generated.cure", line: 9, col: 3, macro: "make"}
    assert [%{keyword: "make", line: 9, col: 3}] = meta[:expansion_provenance]

    info = Metadata.source_info(meta)

    assert [generated, macro] = info.provenance
    assert %{kind: :generated_declaration, name: "generated"} = generated
    assert %{kind: :macro_expansion, name: "make"} = macro
    assert source_slice(@source, info.whole) =~ "lift module Cure.DeclarationMacroActor"
    assert source_slice(@source, macro.invocation) =~ "make lift module Cure.DeclarationMacroActor"
    assert source_slice(@source, macro.definition) == "syntax make <x: Code> computed by id"

    assert Enum.all?(meta[:declarations], fn {_tag, declaration_meta, _children} ->
             declaration_info = Metadata.source_info(declaration_meta)

             declaration_meta[:source_provenance] == meta[:source_provenance] and
               declaration_meta[:expansion_provenance] == meta[:expansion_provenance] and
               Enum.any?(declaration_info.provenance, &(&1.kind == :generated_declaration)) and
               source_slice(@source, declaration_info.whole) != ""
           end)
  end

  # Every macro passes through `Cure.Compiler.MacroFuzz`'s expansion-proof gate at
  # its DEFINITION site: the rule is expanded against generated use-sites and the
  # result is checked. The gate recognised a `{:block, …}` of declarations and a
  # `lift module` request, and sent everything else to the expression checker — so
  # a rule whose template is a single declaration was checked as an expression and
  # rejected with `{:unsupported_expression, {:function_def, …}}`, before any
  # use-site existed. A `becomes` template is ONE expression, so a lone
  # declaration is the only shape a `syntax … becomes fn …` rule can have.
  test "a rule whose template is a single declaration passes the expansion-proof gate" do
    source = """
    mod SingleDeclarationTemplate
      macro Publish
        syntax publish becomes fn made() -> Int = 1
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a single-declaration template is still proved, not waved through" do
    source = """
    mod IllTypedDeclarationTemplate
      macro Publish
        syntax publish becomes fn made() -> Int = true
    """

    assert {:error, reason} = Program.elaborate(source)

    assert {:expansion_ill_typed, %{keyword: "publish"}} = Program.semantic_error(reason)
  end

  # A template may name another module, and the defining module need not import
  # it: the reference does not exist until the rule expands, and it lands in the
  # EXPANDING module, where the canonical pipeline discovers it as a
  # `:macro_generated_reference` edge and extends the dependency graph until it
  # closes. The definition-site proof failing on it made such a template
  # unwritable and reported a module the author had no reason to import.
  test "a template may name a module the defining module does not import" do
    source = """
    mod CrossModuleTemplate
      macro Publish
        syntax publish becomes fn made() -> Int = Some.Other.Module.value()
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  # And the deferral is keyed on the name being QUALIFIED. A bare unresolved name
  # is still a definition-site failure and must stay one — that is exactly how a
  # hygiene defect in a generated binder surfaces, which is the class of bug this
  # gate exists to catch.
  test "a bare unresolved name in a template is still a definition-site failure" do
    source = """
    mod BareUnresolvedTemplate
      macro Publish
        syntax publish becomes fn made() -> Int = no_such_function()
    """

    assert {:error, reason} = Program.elaborate(source)

    assert {:expansion_ill_typed, %{keyword: "publish"}} = Program.semantic_error(reason)
  end

  test "the declaration pass does not consume computed uses in function bodies" do
    source = """
    mod M
      use Std.Syntax
      use Std.List

      macro Mk
        syntax mk computed by build

      fn build(input: Syntax) -> Syntax =
        Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(1))

      fn f() -> Int = mk
    end
    """

    assert {:ok, ast} = Cure.Compiler.parse_source(source)
    assert {:ok, expanded} = Program.expand_declaration_uses(ast)
    assert find_computed_use(expanded)
  end

  test "a raw syntax result receives a friendly generated-expansion diagnostic" do
    source = """
    mod M
      use Std.Syntax
      use Std.Syntax.Raw

      macro Bad
        syntax bad computed by build

      fn build(input: Syntax) -> Syntax = unsafe_raw(SInt(1))
      fn result() -> Int = bad
    end
    """

    # The inner reason is wrapped in `:source_context` so it carries the
    # invocation span; the `:computed_macro_error` payload underneath is
    # unchanged, and the rendering below is what pins the author-facing text.
    assert {:error,
            {:codegen_error,
             {:source_context,
              {:computed_macro_error, meta, {:invalid_generated_syntax, {:raw_syntax_in_expansion, []}}}, _ctx}} =
              reason} =
             Cure.Compiler.compile_and_load(source, emit_events: false)

    assert Keyword.get(meta, :keyword) == "bad"

    rendered =
      Errors.format_error(
        {:codegen_error, {:computed_macro_error, meta, {:invalid_generated_syntax, {:raw_syntax_in_expansion, []}}}},
        "macro.cure"
      )

    assert rendered =~ "invalid macro expansion"
    assert rendered =~ "raw syntax is only valid for reflection"
    assert rendered =~ "macro.cure:9"

    {diagnostic, registry} = Errors.to_diagnostic(reason, "macro_generated.cure", source)

    assert Renderer.plain(diagnostic, registry, width: 80) ==
             String.trim_trailing("""
             -- COMPUTED MACRO EXPANSION FAILED [E092] ----------------- macro_generated.cure

             The `bad` computed macro could not produce valid Cure syntax: invalid macro
             expansion: raw syntax is only valid for reflection, not generated Cure code at
             the expansion root

             at macro_generated.cure:9:24
             9 |   fn result() -> Int = bad
               |                        ^^^ this macro invocation generated the failing syntax

             Note: Edit the authored macro invocation or its rule; generated syntax is not
                   the user-facing source.

             Hint: Return structured `Syntax`; use raw syntax only for reflection

             expansion: bad
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 8, "character" => 23},
             "end" => %{"line" => 8, "character" => 26}
           }
  end

  test "author rejection results retain a friendly macro diagnostic category" do
    rendered =
      Errors.format_error(
        {:codegen_error,
         {:computed_macro_error, [keyword: "actor", line: 4],
          {:author_diagnostics, [{:macro_failure, :missing_state, []}]}}},
        "actor.cure"
      )

    assert rendered =~ "macro rejected expansion"
    assert rendered =~ "reported `missing_state`"
    assert rendered =~ "actor.cure:4"
  end

  test "repeated computed holes are typed and reflected as List(Syntax)" do
    source = """
    mod M
      use Std.Syntax

      macro Gather
        syntax gather <items: Code>... computed by build

      fn build(input: GatherSyntax) -> Syntax =
        match input.items
          [] -> Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(0))
          [_ | _] -> Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(1))

      fn result() -> Int = gather 1 2 3
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 1
  end

  test "a structured family lowers to nested syntax records and expands" do
    source = """
    mod M
      use Std.Syntax
      use Std.Option

      macro custom_actor <name: ModuleName>
        syntax family ActorDefinition
          state Type
          optional initial Expression
        accepts ActorDefinition
        expands with derive_actor

      fn derive_actor(input: ActorDefinitionInputSyntax) -> Syntax = match input.definition.initial
        None() -> int_literal(0)
        Some(value) -> value

      fn result() -> Int = custom_actor Counter
        state Int
        initial 7
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 7
  end

  test "optional family sections are ordinary Option values" do
    source = """
    mod M
      use Std.Syntax
      use Std.Option

      macro actor <name: ModuleName>
        syntax family ActorDefinition
          state Type
          optional initial Expression
        accepts ActorDefinition
        expands with derive_actor

      fn derive_actor(name: ModuleNameSyntax, definition: ActorDefinitionSyntax) -> Syntax =
        match definition.initial
          None() -> int_literal(0)
          Some(value) -> value

      fn absent() -> Int = actor Counter
        state Int

      fn present() -> Int = actor Counter
        state Int
        initial 7
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :absent, []) == 0
    assert apply(module, :present, []) == 7
  end

  test "an optional-only family does not match without consuming a section" do
    source = """
    mod M
      use Std.Syntax

      macro optional_only <name: ModuleName>
        syntax family Definition
          optional initial Expression
        accepts Definition
        expands with expand

      fn expand(name: ModuleNameSyntax, definition: DefinitionSyntax) -> Syntax = int_literal(0)
      fn result() -> Int = optional_only Empty
    end
    """

    assert {:error, {:parse_error, errors}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)

    assert Enum.any?(errors, &match?({:macro_use_mismatch, %{keyword: "optional_only"}}, &1))
  end

  test "a recognized family body diagnoses a missing required section" do
    source = """
    mod M
      use Std.Syntax

      macro complete <name: ModuleName>
        syntax family Definition
          state Type
          optional initial Expression
        accepts Definition
        expands with expand

      fn expand(name: ModuleNameSyntax, definition: DefinitionSyntax) -> Syntax = int_literal(0)
      fn result() -> Int = complete Incomplete
        initial 7
    end
    """

    assert {:error, {:parse_error, errors}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)

    assert Enum.any?(errors, fn
             {:missing_syntax_family_field, %{family: "Definition", field: "state"}} -> true
             _ -> false
           end)

    error = Enum.find(errors, &match?({:missing_syntax_family_field, _}, &1))
    {diagnostic, registry} = Errors.to_diagnostic({:parse_error, [error]}, "missing_family.cure", source)
    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert diagnostic.primary.span.start_line == 13

    assert rendered ==
             String.trim_trailing("""
             -- SYNTAX-FAMILY FIELD IS MISSING [E092] ------------------- missing_family.cure

             The `Definition` syntax family requires a `state` section here.

             at missing_family.cure:13:14
             13 |     initial 7
                |              ^ add `state` here

             Hint: Add a `state ...` section to this family body
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 12, "character" => 13},
             "end" => %{"line" => 12, "character" => 13}
           }
  end

  test "family field mistakes label the authored field and offer a unique repair" do
    source = """
    mod M
      use Std.Syntax

      macro complete <name: ModuleName>
        syntax family Definition
          state Type
          optional initial Expression
        accepts Definition
        expands with expand

      fn expand(name: ModuleNameSyntax, definition: DefinitionSyntax) -> Syntax = int_literal(0)
      fn result() -> Int = complete Broken
        state Int
        inital 7
    end
    """

    assert {:error, {:parse_error, errors}} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert [{:unknown_syntax_family_field, details}] = errors
    assert details.field == "inital"
    assert details.span.start_line == 14
    assert details.span.start_column == 5
    assert details.span.end_column == 11

    {diagnostic, registry} =
      Errors.to_diagnostic({:parse_error, errors}, "unknown_family_field.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- UNKNOWN SYNTAX-FAMILY FIELD [E092] ---------------- unknown_family_field.cure

             `inital` is not a field of the `Definition` syntax family.

             at unknown_family_field.cure:14:5
             14 |     inital 7
                |     ^^^^^^ this field is not declared by the family

             Hint: Replace it with `initial`
             """)

    assert [%{applicability: :machine_applicable, edits: [%{replacement: "initial"}]}] =
             diagnostic.suggestions

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 13, "character" => 4},
             "end" => %{"line" => 13, "character" => 10}
           }
  end

  test "duplicate family fields label both authored sections" do
    source = """
    mod M
      use Std.Syntax

      macro complete <name: ModuleName>
        syntax family Definition
          state Type
        accepts Definition
        expands with expand

      fn expand(name: ModuleNameSyntax, definition: DefinitionSyntax) -> Syntax = int_literal(0)
      fn result() -> Int = complete Broken
        state Int
        state Bool
    end
    """

    assert {:error, {:parse_error, [{:duplicate_syntax_family_field, details}] = errors}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)

    assert details.first_span.start_line == 12
    assert details.span.start_line == 13

    {diagnostic, registry} =
      Errors.to_diagnostic({:parse_error, errors}, "duplicate_family_field.cure", source)

    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- SYNTAX-FAMILY FIELD IS DUPLICATED [E092] -------- duplicate_family_field.cure

             The `state` field may be supplied only once in this family body.

             at duplicate_family_field.cure:13:5
             12 |     state Int
                |     ----- the field was first supplied here
             13 |     state Bool
                |     ^^^^^ this second `state` field is redundant

             Hint: Keep one `state` section
             """)

    lsp = Renderer.lsp(diagnostic, registry)

    assert lsp["range"] == %{
             "start" => %{"line" => 12, "character" => 4},
             "end" => %{"line" => 12, "character" => 9}
           }

    assert [%{"location" => %{"range" => first_range}}] = lsp["relatedInformation"]

    assert first_range == %{
             "start" => %{"line" => 11, "character" => 4},
             "end" => %{"line" => 11, "character" => 9}
           }
  end

  test "primitive family fields underline the non-matching literal" do
    source = """
    mod M
      use Std.Syntax

      macro configure <name: ModuleName>
        syntax family Config
          count Int
        accepts Config
        expands with expand

      fn expand(name: ModuleNameSyntax, config: ConfigSyntax) -> Syntax = int_literal(0)
      fn result() -> Int = configure Broken
        count true
    end
    """

    assert {:error, {:parse_error, [{:expected_literal_capture, details}] = errors}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)

    assert details.shape == "Int"
    assert details.span.start_line == 12
    assert details.span.start_column == 11
    assert details.span.end_column == 15

    {diagnostic, registry} = Errors.to_diagnostic({:parse_error, errors}, "literal_family.cure", source)
    rendered = Renderer.plain(diagnostic, registry, width: 80)

    assert rendered ==
             String.trim_trailing("""
             -- MACRO FIELD NEEDS A LITERAL [E094] ---------------------- literal_family.cure

             This syntax-family field accepts an `Int` literal, not an expression of another
             shape.

             at literal_family.cure:12:11
             12 |     count true
                |           ^^^^ this is not an `Int` literal

             Hint: Replace this value with an `Int` literal
             """)

    assert Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 11, "character" => 10},
             "end" => %{"line" => 11, "character" => 14}
           }
  end

  test "an expression obligation resolves at the macro use site" do
    source = """
    mod M
      use Std.Syntax
      use Std.Beam

      macro Gate
        syntax gated <value: Expression> where BeamEncode(value) computed directly by pass

      fn pass(value: Syntax) -> Syntax = value
      type Identity = Primary | Secondary deriving BeamEncode
      fn result() -> Identity = gated Primary()
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == :Primary
  end

  test "an unsatisfied expression obligation fails before expansion" do
    source = """
    mod M
      use Std.Syntax
      use Std.Beam

      macro Gate
        syntax gated <value: Expression> where BeamEncode(value) computed directly by pass

      fn pass(value: Syntax) -> Syntax = value
      type Identity = Primary | Secondary
      fn result() -> Identity = gated Primary()
    end
    """

    # Wrapped in `:source_context` so the failure carries the span of the
    # definition it was checking; the obligation payload is unchanged.
    assert {:error,
            {:codegen_error,
             {:source_context, {:macro_capture_obligation_failed, "gated", "BeamEncode", "value", {:no_instance, _, _}},
              _ctx}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "repeated and one_or_more family sections are ordinary lists" do
    source = """
    mod M
      use Std.Syntax

      macro collect <name: ModuleName>
        syntax family Values
          repeated item Int
          one_or_more required Int
        accepts Values
        expands with count_values

      fn count_values(name: ModuleNameSyntax, definition: ValuesSyntax) -> Syntax =
        int_literal(count(definition.item) + count(definition.required))

      fn count(values: List(Int)) -> Int = match values
        [] -> 0
        [_ | rest] -> 1 + count(rest)

      fn result() -> Int = collect Values
        item 1
        item 2
        required 3
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 3
  end

  test "a repeated custom production becomes a typed nested family record" do
    source = """
    mod M
      use Std.Syntax
      use Std.Option

      macro machine <name: ModuleName>
        syntax family Transition
          syntax <from: Name> --<event: Name>--> <to: Name>
        syntax family Definition
          one_or_more transitions Transition
        accepts Definition
        expands with build

      fn build(name: ModuleNameSyntax, definition: DefinitionSyntax) -> Syntax =
        match definition.transitions
          [first | _] -> match tag(first.from) == :variable
            true -> int_literal(1)
            false -> int_literal(0)
          [] -> int_literal(0)

      fn result() -> Int = machine Turnstile
        Locked --Coin--> Unlocked
        Unlocked --Push--> Locked
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 1
  end

  test "a named section groups repeated nested production records" do
    source = """
    mod M
      use Std.Syntax
      use Std.Option

      macro machine <name: ModuleName>
        syntax family Transition
          syntax <from: Name> --<event: Name>--> <to: Name>
          optional update Expression
        syntax family Definition
          one_or_more transitions Transition
        accepts Definition
        expands with build

      fn build(name: ModuleNameSyntax, definition: DefinitionSyntax) -> Syntax =
        match definition.transitions
          [first, second] -> match second.update
            Some(value) -> value
            None() -> int_literal(0)
          _ -> int_literal(0)

      fn result() -> Int = machine Turnstile
        transitions
          Locked --Coin--> Unlocked
          Unlocked --Push--> Locked
            update 7
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 7
  end

  test "a structured expander may receive leading captures directly" do
    source = """
    mod M
      use Std.Syntax
      use Std.Option

      macro actor <name: ModuleName>
        syntax family ActorDefinition
          state Type
          optional initial Expression
        accepts ActorDefinition
        expands with derive_actor

      fn derive_actor(name: ModuleNameSyntax, definition: ActorDefinitionSyntax) -> Syntax = match definition.initial
        None() -> int_literal(0)
        Some(value) -> value

      fn result() -> Int = actor Counter
        state Int
        initial 9
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 9
  end

  test "a structured family can include a reusable family without duplicating fields" do
    source = """
    mod M
      use Std.Syntax
      use Std.Option

      macro service <name: ModuleName>
        syntax family CommonDefinition
          state Type

        syntax family ServiceDefinition
          includes CommonDefinition
          optional limit Int

        accepts ServiceDefinition
        expands with derive_service

      fn derive_service(name: ModuleNameSyntax, definition: ServiceDefinitionSyntax) -> Syntax =
        match definition.limit
          None() -> int_literal(0)
          Some(value) -> int_literal(value)

      fn result() -> Int = service Counter
        state Int
        limit 9
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == 9
  end

  test "a primitive literal capture is passed as its semantic Cure value" do
    source = """
    mod M
      use Std.Syntax

      macro log
        syntax log <level: Atom> computed by build

      fn build(level: Atom) -> Syntax =
        Leaf(:literal, [KV(:subtype, SAtom(:symbol))], SAtom(level))

      fn result() -> Atom = log :hello
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == :hello
  end

  test "a computed expander may return an explicit MacroResult" do
    source = """
    mod M
      use Std.Syntax

      macro log
        syntax log <level: Atom> computed by build

      fn build(level: Atom) -> MacroResult =
        expand(Leaf(:literal, [KV(:subtype, SAtom(:symbol))], SAtom(level)))

      fn result() -> Atom = log :hello
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == :hello
  end

  test "a computed expander may return Std.Result for convenience" do
    source = """
    mod M
      use Std.Syntax
      use Std.Result

      macro log
        syntax log <level: Atom> computed by build

      fn build(level: Atom) -> Result(Syntax, Syntax) =
        ok(Leaf(:literal, [KV(:subtype, SAtom(:symbol))], SAtom(level)))

      fn result() -> Atom = log :hello
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == :hello
  end

  test "a rejected MacroResult stops compilation before runtime code exists" do
    source = """
    mod M
      use Std.Syntax

      macro log
        syntax log <level: Atom> computed by build

      fn build(level: Atom) -> MacroResult = reject(atom_literal(:invalid_level))

      fn result() -> Atom = log :hello
    end
    """

    assert {:error, _reason} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "repeated primitive captures arrive as ordinary Cure lists" do
    source = """
    mod M
      use Std.Syntax

      macro tags
        syntax tags <values: Atom>... computed by build

      fn build(input: TagsSyntax) -> Syntax =
        match input.values
          [] -> atom_literal(:empty)
          [_ | _] -> atom_literal(:nonempty)

      fn result() -> Atom = tags :one :two
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(module, :result, []) == :nonempty
  end

  test "nested primitive family fields arrive as ordinary Cure values" do
    source = """
    mod M
      use Std.Syntax

      macro value
        syntax family Definition
          initial Int
        accepts Definition
        expands with build

      fn build(definition: DefinitionSyntax) -> Syntax = integer(definition.initial)

      fn result() -> Int = value
        initial 7
    end
    """

    assert {:ok, module} = Cure.Compiler.compile_and_load(source, emit_events: false)

    assert apply(module, :result, []) == 7
  end

  test "absent optional computed holes retain their reflected field slot" do
    source = """
    mod M
      use Std.Syntax

      macro Optional
        syntax opt (<value: Code>)? computed by identity

      fn identity(input: OptSyntax) -> Syntax = Leaf(:literal, [KV(:subtype, SAtom(:integer))], SInt(0))
      fn result() -> Syntax = opt
    end
    """

    assert {:ok, ast} = Cure.Compiler.parse_source(source)
    assert {:ok, [nil]} = find_computed_input(ast)
  end

  defp find_computed_input({:computed_use, _meta, [_elab, {:macro_input, _input_meta, children}]}),
    do: {:ok, children}

  defp find_computed_input({:function_def, _meta, body}), do: find_computed_input(body)

  defp find_computed_input({_tag, _meta, children}) when is_list(children) do
    Enum.find_value(children, :not_found, fn child ->
      case find_computed_input(child) do
        :not_found -> nil
        result -> result
      end
    end)
  end

  defp find_computed_input(list) when is_list(list) do
    Enum.find_value(list, :not_found, fn child ->
      case find_computed_input(child) do
        :not_found -> nil
        result -> result
      end
    end)
  end

  defp find_computed_input(_other), do: :not_found

  defp find_computed_use({:computed_use, _meta, _children}), do: true
  defp find_computed_use({:function_def, _meta, body}), do: find_computed_use(body)

  defp find_computed_use({_tag, _meta, children}) when is_list(children),
    do: Enum.any?(children, &find_computed_use/1)

  defp find_computed_use(list) when is_list(list), do: Enum.any?(list, &find_computed_use/1)
  defp find_computed_use(_other), do: false

  defp find_lift_module({:lift_module, _meta, _children} = node), do: node

  defp find_lift_module({_tag, _meta, children}) when is_list(children),
    do: Enum.find_value(children, &find_lift_module/1)

  defp find_lift_module(list) when is_list(list), do: Enum.find_value(list, &find_lift_module/1)
  defp find_lift_module(_other), do: nil
end
