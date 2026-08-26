defmodule Cure.Compiler.LiftModuleSurfaceTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Errors, Lexer, LiftModule, Parser}
  alias Cure.Diagnostic.Renderer

  test "lift module parses behaviour and quoted callback bodies as pure data" do
    source = """
    lift module Cure.Generated.Worker
      behaviour GenServer
      callback init(arg: Int) -> arg
      callback handle_info(msg: Int, state: Int) -> state
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:lift_module, meta, []}} = Parser.parse(tokens, emit_events: false)
    assert meta[:module] == "Cure.Generated.Worker"
    assert meta[:behaviour] == :GenServer

    assert Enum.map(meta[:callbacks], &{&1.name, &1.arity}) == [
             {:init, 1},
             {:handle_info, 2}
           ]

    assert meta[:callbacks]
           |> Enum.map(& &1.callback_context)
           |> Enum.map(&Map.take(&1, [:behaviour, :callback, :arity])) == [
             %{behaviour: :GenServer, callback: :init, arity: 1},
             %{behaviour: :GenServer, callback: :handle_info, arity: 2}
           ]

    assert %{
             parameter_names: ["arg"],
             parameter_types: [{:variable, _, "Int"}],
             return_annotation: :inferred,
             return_type: nil
           } =
             hd(meta[:callbacks]).callback_context

    assert %{
             parameter_names: ["msg", "state"],
             parameter_types: [{:variable, _, "Int"}, {:variable, _, "Int"}],
             return_annotation: :inferred,
             return_type: nil
           } =
             List.last(meta[:callbacks]).callback_context

    assert {:variable, _, "arg"} = hd(meta[:callbacks]).body

    assert {:ok, %{kind: :quoted_module, behaviour: :GenServer}} =
             LiftModule.request_ast({:lift_module, meta, []})
  end

  test "lifted callback context carries parameter and return type syntax" do
    source = """
    lift module Cure.Generated.Context
      behaviour custom_behavior
      callback ping(arg: Int, flag: Bool) returns Tuple(Int, Bool) = %[arg, flag]
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:lift_module, meta, []}} = Parser.parse(tokens, emit_events: false)

    [callback] = meta[:callbacks]

    assert [
             {:variable, _, "Int"},
             {:variable, _, "Bool"}
           ] = callback.callback_context.parameter_types

    assert {:tuple_type, _, _} = callback.callback_context.return_type
  end

  test "generic lifted modules accept user-defined behavior atoms" do
    source = """
    mod M
      macro Lift
        syntax custom <name: ModuleName> becomes lift module name
          behaviour custom_behavior
          fn ping() -> Int = 1
      custom Cure.Generated.Custom
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    assert {:lift_module, meta, []} = List.last(children)
    assert meta[:behaviour] == :custom_behavior
    assert {:ok, request} = LiftModule.request_ast({:lift_module, meta, []})
    assert request.behaviour == :custom_behavior
  end

  test "compilation reports an invalid lifted module name before codegen" do
    source = "lift module Elixir.Bad\n  behaviour custom_behavior\n"

    assert {:error, {:invalid_module_name, "Elixir.Bad"}} =
             Cure.Compiler.compile_string(source, emit_events: false)
  end

  test "computed syntax may provide a reflected atom module name" do
    ast = {:lift_module, [module: :"Cure.Generated.Atom", behaviour: :custom_behavior], []}

    assert {:ok, request} = LiftModule.request_ast(ast)
    assert request.module == "Cure.Generated.Atom"
  end

  test "lifted-module validation preserves the specific rejected field" do
    base = [module: "Cure.Generated.Valid", behaviour: :custom_behavior]

    assert {:error, {:invalid_module_name, "bad.name"}} =
             LiftModule.request_ast({:lift_module, Keyword.put(base, :module, "bad.name"), []})

    assert {:error, {:invalid_behaviour, nil}} =
             LiftModule.request_ast({:lift_module, Keyword.put(base, :behaviour, nil), []})

    assert {:error, :invalid_lift_callback} =
             LiftModule.request_ast({:lift_module, Keyword.put(base, :callbacks, :callbacks), []})

    assert {:error, :invalid_lift_callback} =
             LiftModule.request_ast({:lift_module, Keyword.put(base, :callbacks, [%{name: "ping", arity: 0}]), []})

    assert {:error, :invalid_lift_declaration} =
             LiftModule.request_ast({:lift_module, Keyword.put(base, :declarations, [42]), []})

    assert {:error, :invalid_lift_import} =
             LiftModule.request_ast({:lift_module, Keyword.put(base, :imports, [:not_text]), []})

    assert {:error, :invalid_lift_inheritance} =
             LiftModule.request_ast({:lift_module, Keyword.put(base, :inherit_imports, :sometimes), []})

    assert {:error, :invalid_lift_module_ast} = LiftModule.request_ast({:lift_module, [42], []})
    assert {:error, :invalid_lift_module_ast} = LiftModule.request_ast(:not_a_lifted_module)
    assert {:error, {:invalid_lift_module, :request}} = LiftModule.emit(:request)
  end

  test "every lifted-module validation branch has dedicated diagnostic content" do
    cases = [
      {{:invalid_lift_module, :request}, "Lifted module request is malformed",
       "BEAM emission expected a validated lifted-module request.",
       "Build the request from a valid `lift module` declaration"},
      {:invalid_lift_module_ast, "Lifted module syntax is malformed",
       "A lifted module must be represented by one well-formed `lift_module` syntax node.",
       "Use a `lift module` declaration with a name and body"},
      {{:invalid_lift_module_name, "Worker"}, "Lifted module name is outside Cure",
       "The generated module `Worker` is not beneath the `Cure` namespace required for lifted code.",
       "Use a module name beginning with `Cure.`"},
      {{:invalid_module_name, "bad.name"}, "Lifted module name is invalid",
       "`bad.name` is not a valid qualified module name; every segment must begin with an uppercase letter.",
       "Use a name such as `Cure.Generated.Worker`"},
      {{:invalid_behaviour, nil}, "Lifted module behaviour is invalid",
       "A lifted module needs a non-empty atom naming its BEAM behaviour, but this declaration uses `nil`.",
       "Use the atom naming the implemented BEAM behaviour"},
      {:invalid_lift_callback, "Lifted module callback is malformed",
       "Every lifted callback needs an atom name, a non-negative arity, parameters, return type, body, and source line.",
       "Provide a complete callback declaration matching the behaviour"},
      {:invalid_lift_declaration, "Lifted module declaration is malformed",
       "Every declaration copied into a lifted module must be quoted Cure syntax.",
       "Provide quoted declaration nodes in the lifted module body"},
      {:invalid_lift_import, "Lifted module import is malformed",
       "Every lifted-module dependency must be a textual qualified module name.",
       "Use qualified import names such as `Std.Actor`"},
      {:invalid_lift_inheritance, "Lifted module inheritance option is invalid",
       "The `inherit_imports` option must be either `true` or `false`.",
       "Use `true` to inherit enclosing imports or `false` to isolate them"},
      {{:lifted_module_dependency_cycle, "Cure.A"}, "Lifted modules form a dependency cycle",
       "The generated module `Cure.A` is reached again while ordering lifted-module dependencies.",
       "Remove or redirect one dependency in the cycle"},
      {{:duplicate_lifted_module, "Cure.Worker"}, "Lifted module name is repeated",
       "More than one generated declaration produces `Cure.Worker`, so the compiler cannot choose one module body.",
       "Give every lifted module a unique qualified name"}
    ]

    Enum.each(cases, fn {reason, title, body, hint} ->
      {diagnostic, registry} = Errors.to_diagnostic(reason, "lift.cure", "")
      output = Renderer.plain(diagnostic, registry, width: 80)

      assert diagnostic.code == "E092"
      assert diagnostic.key == :lift_module_validation
      assert diagnostic.title == title
      assert String.replace(output, ~r/\s+/, " ") =~ String.replace(body, ~r/\s+/, " ")
      assert output =~ "Hint: " <> hint

      lsp = Renderer.lsp(diagnostic, registry)
      refute Map.has_key?(lsp, "range")
      assert lsp["message"] == title <> "\n\n" <> body
    end)
  end

  test "lifted callback return types are preserved as ordinary function annotations" do
    source = """
    lift module Cure.Generated.Typed
      behaviour custom_behavior
      callback ping(arg: Int) returns Int = arg
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:lift_module, meta, []}} = Parser.parse(tokens, emit_events: false)
    assert [%{return_type: {:variable, _, "Int"}}] = meta[:callbacks]
  end

  test "lifted callback return mismatches fail ordinary elaboration" do
    source = """
    lift module Cure.Generated.BadCallback
      behaviour custom_behavior
      callback ping(arg: Int) returns Bool = arg
    """

    assert {:error, _} = Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "a transparent macro can substitute an identifier into lift module" do
    source = """
    mod M
      macro Lift
        syntax liftit <name: ModuleName> becomes lift module name
          behaviour GenServer
          fn module_name() -> Atom = name
      liftit Cure.Generated.Worker
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    assert {:lift_module, meta, []} = List.last(children)
    assert meta[:module] == "Cure.Generated.Worker"
    assert meta[:source_provenance].file == "nofile"

    assert [{:function_def, _, [{:literal, [subtype: :symbol], :"Cure.Generated.Worker"}]}] =
             Cure.MetaAST.Metadata.strip_diagnostics(meta[:declarations])
  end

  test "a delayed callback body expands beam_ops after the callback context is introduced" do
    source = """
    mod Host
      use Std.Otp
      macro Lift
        syntax lift <name: ModuleName> <body: delayed raw until dedent> contextual becomes lift module name
          use Std.Otp
          behaviour custom_behavior
          callback ping(arg: Int) returns Effect(Pid(Atom)) = body
      lift Cure.Generated.Contextual
        beam_ops self
    """

    assert {:ok, main} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert main == :"Cure.Host"
    assert function_exported?(:"Cure.Generated.Contextual", :ping, 1)
  end

  test "a transparent macro parses a raw body splice into ordinary declarations" do
    source = """
    mod M
      macro Lift
        syntax one becomes 42
        syntax liftit <name: ModuleName> <body: raw until dedent> becomes lift module name
          behaviour GenServer
          callback init(arg: Int) -> arg
          fn module_name() -> Atom = name
          body
      liftit Cure.Generated.Worker
        fn helper(arg: Int) -> Int = one
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, {:container, _, children}} = Parser.parse(tokens, emit_events: false)
    assert {:lift_module, meta, []} = List.last(children)
    assert meta[:module] == "Cure.Generated.Worker"

    assert [
             {:function_def, module_meta, [{:literal, [subtype: :symbol], :"Cure.Generated.Worker"}]},
             {:function_def, helper_meta, [{:literal, _, 42}]}
           ] = Cure.MetaAST.Metadata.strip_diagnostics(meta[:declarations])

    assert module_meta[:name] == "module_name"
    assert helper_meta[:name] == "helper"
  end

  test "a transparent macro can compile a parsed raw body splice" do
    source = """
    mod Main
      macro Lift
        syntax one becomes 42
        syntax liftit <name: ModuleName> <body: raw until dedent> becomes lift module name
          behaviour GenServer
          callback init(arg: Int) -> arg
          fn module_name() -> Atom = name
          body
      liftit Cure.Generated.Worker
        fn helper(arg: Int) -> Int = one
    """

    assert {:ok, main} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert main == :"Cure.Main"
    assert function_exported?(:"Cure.Generated.Worker", :init, 1)
    assert apply(:"Cure.Generated.Worker", :init, [42]) == 42
    assert apply(:"Cure.Generated.Worker", :module_name, []) == :"Cure.Generated.Worker"
  end

  test "macro lexical imports qualify bare types and functions in lifted output" do
    source = """
    mod Host
      use Std.Supervisor
      macro Lift
        syntax make <name: ModuleName> becomes lift module name
          behaviour custom_behavior
          fn build() -> StrategySpec = supervision_strategy(one_for_all(), 2, more(8))
      make Cure.Generated.BareNames
    """

    assert {:ok, _host} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.BareNames", :build, []) == {:one_for_all, 2, 9}
  end

  test "macro lexical imports preserve aliases in lifted output" do
    source = """
    mod Host
      use Std.Supervisor as Sup
      macro Lift
        syntax make <name: ModuleName> becomes lift module name
          behaviour custom_behavior
          fn build() -> Sup.StrategySpec = Sup.supervision_strategy(Sup.one_for_all(), 2, Sup.more(8))
      make Cure.Generated.AliasedNames
    """

    assert {:ok, _host} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert apply(:"Cure.Generated.AliasedNames", :build, []) == {:one_for_all, 2, 9}
  end

  test "a transparent lift can start its generated gen_server through Std.Otp" do
    source = """
    mod Main
      macro Lift
        syntax server <name: ModuleName> becomes lift module name
          use Std.Otp
          behaviour GenServer
          callback init(arg: Int) -> %[:ok, arg]
          fn start_link(arg: Int) -> Effect(Tuple) = Std.Otp.start_link(name, [arg])
      server Cure.Generated.Server
    """

    assert {:ok, main} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert main == :"Cure.Main"
    assert {:ok, pid} = apply(:"Cure.Generated.Server", :start_link, [42])
    assert is_pid(pid)
    :gen_server.stop(pid)
  end

  test "lifted modules compile as independent units through the common emitter" do
    source = """
    mod Main
      lift module Cure.Generated.Worker
        behaviour GenServer
        callback init(arg: Int) -> arg
    """

    assert {:ok, main} = Cure.Compiler.compile_and_load(source, emit_events: false)
    assert main == :"Cure.Main"
    assert function_exported?(:"Cure.Generated.Worker", :init, 1)
    assert apply(:"Cure.Generated.Worker", :init, [42]) == 42
  end

  test "duplicate lifted module names are rejected before emission" do
    source = """
    mod Main
      lift module Cure.Generated.Worker
        behaviour GenServer
        callback init(arg: Int) -> arg
      lift module Cure.Generated.Worker
        behaviour GenServer
        callback init(arg: Int) -> arg
    """

    assert {:error, {:codegen_error, {:duplicate_lifted_module, "Cure.Generated.Worker"}}} =
             Cure.Compiler.compile_and_load(source, emit_events: false)
  end

  test "lifted modules are ordered after generated modules they import" do
    source = """
    mod Main
      lift module Cure.Generated.Root
        behaviour GenServer
        use Cure.Generated.Worker
        callback init(arg: Int) -> arg
      lift module Cure.Generated.Worker
        behaviour GenServer
        callback init(arg: Int) -> arg
    """

    assert {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    assert {:ok, ast} = Parser.parse(tokens, emit_events: false)
    assert {:ok, requests} = LiftModule.collect(ast)
    assert Enum.map(requests, & &1.module) == ["Cure.Generated.Worker", "Cure.Generated.Root"]
    assert [root] = Enum.filter(requests, &(&1.module == "Cure.Generated.Root"))
    assert root.dependencies == ["Cure.Generated.Worker"]
  end

  test "lifted module dependency cycles are rejected before emission" do
    ast =
      {:container, [],
       [
         {:lift_module,
          [
            module: "Cure.A",
            behaviour: :GenServer,
            callbacks: [%{name: :init, arity: 1}],
            declarations: [{:import, [source: "Cure.B"], []}]
          ], []},
         {:lift_module,
          [
            module: "Cure.B",
            behaviour: :GenServer,
            callbacks: [%{name: :init, arity: 1}],
            declarations: [{:import, [source: "Cure.A"], []}]
          ], []}
       ]}

    assert {:error, {:lifted_module_dependency_cycle, _}} = LiftModule.collect(ast)
  end
end
