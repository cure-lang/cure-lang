defmodule Cure.Diagnostic.HostTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Host

  test "renders structured compiler failures through the shared diagnostic model" do
    source = "fn run() -> Int = missing_name\n"

    rendered =
      Host.render(
        {:source_context, {:unknown_global, "missing_name"}, %{line: 1, column: 20}},
        "demo.cure",
        source
      )

    assert rendered =~ "[E091]"
    assert rendered =~ "missing_name"
    assert rendered =~ "demo.cure"
    assert rendered =~ "^"
  end

  test "exposes structured conversion for embedded sinks" do
    {diagnostic, registry} = Host.to_diagnostic({:unknown_global, "missing_name"}, "repl.cure", "")

    assert diagnostic.code == "E091"
    assert registry != nil

    assert Cure.Diagnostic.Sink.new(format: :json, registry: registry)
           |> Cure.Diagnostic.Sink.emit(diagnostic)
           |> Cure.Diagnostic.Sink.render_all()
           |> hd()
           |> Map.fetch!("code") == "E091"
  end

  test "emits diagnostics through a caller-selected device" do
    {:ok, device} = StringIO.open("")
    diagnostic = Cure.Diagnostic.Operational.file_read("demo.cure", :enoent)

    assert {:ok, _sink} = Host.emit_diagnostic(diagnostic, output_device: device, color: :never)
    {_input, output} = StringIO.contents(device)
    assert output =~ "[E095]"
    assert output =~ "Cannot read `demo.cure`"
  end

  test "renders operational failures without fabricating source context" do
    rendered = Host.render({:file_read_error, "demo.cure", :enoent}, "demo.cure")

    assert rendered =~ "[E095]"
    assert rendered =~ "Cannot read `demo.cure`"
    refute rendered =~ "^"

    contextual =
      Cure.Compiler.Errors.format_with_source(
        {:file_read_error, "demo.cure", :enoent},
        "demo.cure",
        "fn run() -> Int = 1\n"
      )

    assert contextual =~ "[E095]"
    refute contextual =~ "| fn run"
  end

  test "source-aware migration warnings resolve their reported line" do
    source = "line one\nline two\nline three\n"

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:migration_warning, %{rule: :legacy, file: "demo.cure", line: 2, message: "migrate this"}},
        "demo.cure",
        source
      )

    assert diagnostic.primary.span.start_line == 2
    assert diagnostic.primary.span.start_byte == byte_size("line one\n")

    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry)
    assert rendered =~ "2 | line two"
    assert rendered =~ "^"
  end

  test "Host preserves a source registry for operational warning carets" do
    source = "line one\nline two\nline three\n"

    {diagnostic, registry} =
      Host.to_diagnostic(
        {:migration_warning, %{rule: :legacy, file: "demo.cure", line: 2, message: "migrate this"}},
        "demo.cure",
        source
      )

    assert registry != nil
    assert diagnostic.primary.span.start_line == 2
    assert diagnostic.primary.span.end_column == 9
    assert Cure.Diagnostic.Renderer.plain(diagnostic, registry) =~ "^^^^^^^^ rule legacy applies here"
  end

  test "Host attaches source carets to line-based compiler warnings" do
    source = "line one\nline two\nline three\n"

    {diagnostic, registry} =
      Host.to_diagnostic(
        {:compiler_warning, %{file: "demo.cure", line: 3, message: "check this"}},
        "demo.cure",
        source
      )

    assert diagnostic.primary.span.start_line == 3
    assert diagnostic.primary.span.end_column == 11
    assert diagnostic.primary.message == "warning applies here"
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry)
    assert rendered =~ "3 | line three"
    assert rendered =~ "^^^^^^^^^^ warning applies here"

    assert Jason.decode!(Cure.Diagnostic.Renderer.json(diagnostic))["primary"]["span"]["start_line"] == 3

    assert Cure.Diagnostic.Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 2, "character" => 0},
             "end" => %{"line" => 2, "character" => 10}
           }
  end

  test "renders macro syntax failures as contextual syntax diagnostics" do
    source = "fn run() -> Int = say nope\n"
    {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, file: "demo.cure", emit_events: false)
    mismatch = Enum.find(tokens, &(&1.value == "nope"))

    rendered =
      Host.render(
        {:macro_use_mismatch,
         %{
           keyword: "say",
           expected: {:literal, "hello"},
           got: "nope",
           token_type: :identifier,
           span: mismatch.span,
           line: mismatch.line,
           column: mismatch.col
         }},
        "demo.cure",
        source
      )

    assert rendered =~ "[E094]"
    assert rendered =~ "MACRO SYNTAX DOES NOT MATCH"
    assert rendered =~ "demo.cure"
    refute rendered =~ ":macro_use_mismatch"

    assert Cure.Compiler.Errors.format_with_source(
             {:macro_use_mismatch,
              %{
                keyword: "say",
                expected: {:literal, "hello"},
                got: "nope",
                token_type: :identifier,
                span: mismatch.span,
                line: mismatch.line,
                column: mismatch.col
              }},
             "demo.cure",
             source
           ) =~ "[E094]"
  end

  test "expected-token syntax failures retain the authored token spelling" do
    source = "fn run(] -> Int = 1\n"
    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, file: "syntax.cure", emit_events: false)
    token = Enum.find(tokens, &(&1.type == :rbracket))

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:expected_token, :rparen, :rbracket, "]", token.line, token.col, token.span},
        "syntax.cure",
        source
      )

    assert diagnostic.code == "E094"
    assert diagnostic.payload.observed == "]"
    assert diagnostic.payload.context.token_type == :rbracket

    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry)

    assert rendered ==
             String.trim_trailing("""
             -- CLOSING DELIMITER DOES NOT MATCH [E094] ------------------------- syntax.cure

             This construct needs ')', but it is closed with ']' instead.

             at syntax.cure:1:8
             1 | fn run(] -> Int = 1
               |        ^ replace this mismatched delimiter

             Hint: Replace ']' with `)`
             """)

    assert [%{applicability: :machine_applicable, edits: [%{span: edit_span, replacement: ")"}]}] =
             diagnostic.suggestions

    assert edit_span == token.span

    assert [%{"newText" => ")", "range" => range}] =
             Cure.Diagnostic.Renderer.lsp(diagnostic, registry)["data"]["suggestions"]
             |> hd()
             |> Map.fetch!("edits")

    assert range == %{
             "start" => %{"line" => 0, "character" => 7},
             "end" => %{"line" => 0, "character" => 8}
           }
  end

  test "parser-owned expected-token spans survive the compiler boundary" do
    source = "fn run(] -> Int = 1\n"
    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, file: "syntax.cure", emit_events: false)
    token = Enum.find(tokens, &(&1.type == :rbracket))

    {diagnostic, _registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:expected_token, :rparen, :rbracket, "]", token.line, token.col, token.span},
        "syntax.cure",
        source
      )

    assert diagnostic.primary.span.start_byte == token.span.start_byte
    assert diagnostic.primary.span.end_byte == token.span.end_byte
    span = diagnostic.primary.span
    assert binary_part(source, span.start_byte, span.end_byte - span.start_byte) == "]"
  end

  test "canonical module-pipeline envelopes preserve the inner syntax diagnostic" do
    source = "fn run(] -> Int = 1\n"
    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, file: "syntax.cure", emit_events: false)
    token = Enum.find(tokens, &(&1.type == :rbracket))

    reason =
      {:module_skeleton_error, {"fixture", "Broken"},
       [{:expected_token, :rparen, :rbracket, "]", token.line, token.col, token.span}]}

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "syntax.cure", source)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry)

    assert diagnostic.code == "E094"
    assert diagnostic.payload.pipeline_stage == :module_skeleton
    assert diagnostic.payload.module_identity == {"fixture", "Broken"}
    assert rendered =~ "CLOSING DELIMITER DOES NOT MATCH"
    refute rendered =~ "INTERNAL COMPILER ERROR"
  end

  test "parser-owned keyword expectation spans survive the compiler boundary" do
    source = "fn run() = with x\n"
    assert {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, file: "keyword.cure", emit_events: false)
    token = Enum.find(tokens, &(&1.type == :newline))

    {diagnostic, _registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:expected, :in, :got, :newline, token.line, token.col, token.span},
        "keyword.cure",
        source
      )

    assert diagnostic.code == "E094"
    assert diagnostic.primary.span.start_line == 1
    assert diagnostic.payload.expected == :in
  end

  test "blames computed macro rejection on the authored invocation" do
    source = "fn run() -> Int = actor()\n"

    rendered =
      Host.render(
        {:computed_macro_error, [keyword: "actor", line: 1, col: 20],
         {:invalid_generated_syntax, {:raw_syntax_in_expansion, []}}},
        "demo.cure",
        source
      )

    assert rendered =~ "[E092]"
    assert rendered =~ "actor"
    assert rendered =~ "demo.cure"
    refute rendered =~ ":computed_macro_error"
  end

  test "computed macro source context does not fabricate a byte-zero span" do
    source = "fn run() -> Int = actor()\n"

    {diagnostic, _registry} =
      Host.to_diagnostic(
        {:computed_macro_error, [keyword: "actor", line: 1, col: 20],
         {:invalid_generated_syntax, {:raw_syntax_in_expansion, []}}},
        "demo.cure",
        source
      )

    assert diagnostic.primary.span.start_byte == :binary.match(source, "actor") |> elem(0)
    refute diagnostic.primary.span.start_byte == 0
  end

  test "converts code generation and BEAM lint failures to a stable internal code" do
    assert Host.render({:codegen_error, :bad_artifact}, "demo.cure") =~
             "[E101]"

    rendered = Host.render({:beam_lint_error, [], []}, "demo.cure")
    assert rendered =~ "[E101]"
    refute rendered =~ ":beam_lint_error"

    assert Cure.Compiler.Errors.format_with_source(
             {:beam_lint_error, [], []},
             "demo.cure",
             "fn run() -> Int = 1\n"
           ) =~ "[E101]"

    assert Cure.Compiler.Errors.format_with_source(
             {:codegen_error, :bad_artifact},
             "demo.cure",
             "fn run() -> Int = 1\n"
           ) =~ "[E101]"
  end

  test "E101 fallback describes structured reasons containing source spans without crashing" do
    span = %Cure.Diagnostic.Span{
      source_id: "demo.cure",
      path: "demo.cure",
      start_byte: 0,
      end_byte: 2,
      start_line: 1,
      start_column: 1,
      end_line: 1,
      end_column: 3
    }

    rendered = Host.render({:codegen_error, {:unexpected_backend_state, %{span: span}}}, "demo.cure")

    assert rendered =~ "CODE GENERATION FAILED [E101]"
    assert rendered =~ "unexpected_backend_state"
    assert rendered =~ "end_line=1"
    refute rendered =~ "Protocol.UndefinedError"
  end

  test "includes the unresolved stdlib module in E101 code-generation failures" do
    rendered =
      Host.render(
        {:codegen_error,
         {:missing_stdlib_module, :"Cure.Std.Missing",
          "use Std.Missing: module 'Cure.Std.Missing' not found. Set CURE_LIB."}},
        "demo.cure"
      )

    assert rendered =~ "STDLIB MODULE RESOLUTION FAILED [E101]"
    assert rendered =~ "Cure.Std.Missing"
    assert rendered =~ "Set CURE_LIB"
  end

  test "canonical emission input failures retain their module and pipeline stage" do
    {diagnostic, registry} =
      Host.to_diagnostic({:beam_emission_input_missing, "Std.Actor"}, "lib/std/actor.cure")

    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 100)

    assert diagnostic.code == "E101"
    assert diagnostic.payload.stage == :canonical_beam_emission
    assert diagnostic.payload.module == "Std.Actor"
    assert diagnostic.payload.file == "lib/std/actor.cure"
    assert diagnostic.payload.reason =~ "beam_emission_input_missing"
    assert diagnostic.payload.fingerprint =~ ~r/^[0-9a-f]{12}$/
    assert rendered =~ "Stage: `canonical_beam_emission`."
    assert rendered =~ "Module: `Std.Actor`."
  end

  test "converts BEAM writer boundary failures without exposing raw tuples" do
    assert Host.render({:write_failed, "_build/Demo.beam", :eacces}, "demo.cure") =~
             "[E096]"

    loaded = Host.render({:load_failed, :badfile}, "demo.cure")
    assert loaded =~ "[E098]"
    refute loaded =~ ":load_failed"

    compiled = Host.render({:compilation_failed, [{:bad_form, :detail}]}, "demo.cure")
    assert compiled =~ "[E098]"
    refute compiled =~ ":compilation_failed"
  end

  test "renders trusted Final-Core rejection paths as structured internal diagnostics" do
    source = "fn run() -> Int = 1\n"

    span = %Cure.Diagnostic.Span{
      source_id: "demo.cure",
      path: "demo.cure",
      start_byte: 0,
      end_byte: 19,
      start_line: 1,
      start_column: 1,
      end_line: 1,
      end_column: 20
    }

    error =
      {:source_context,
       {:final_core_violation, :"Demo#run", [%{clause: :no_hole, message: "hole present in Core term"}]},
       %{
         span: span,
         checking: :"Demo#run",
         codegen_stage: :final_core_validation,
         codegen_module: :"Cure.Demo"
       }}

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(error, "demo.cure", source)
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 80)
    fingerprint = diagnostic.payload.fingerprint

    assert fingerprint =~ ~r/^[0-9a-f]{12}$/

    assert rendered ==
             String.trim_trailing("""
             -- FINAL-CORE VALIDATION FAILED [E101] ------------------------------- demo.cure

             The compiler rejected an internal Core term at the trusted boundary (hole
             present in Core term).

             Stage: `final_core_validation`. Module: `Cure.Demo`. Source: `demo.cure`.
             Declaration: `Demo#run`. Diagnostic fingerprint: `#{fingerprint}`.

             at demo.cure:1:1
             1 | fn run() -> Int = 1
               | ^^^^^^^^^^^^^^^^^^^ this definition produced invalid internal Core

             Note: This is an internal compiler failure; report it with the diagnostic
                   fingerprint.
             """)

    assert Cure.Diagnostic.Renderer.lsp(diagnostic, registry)["range"] == %{
             "start" => %{"line" => 0, "character" => 0},
             "end" => %{"line" => 0, "character" => 19}
           }

    assert diagnostic.payload.stage == :final_core_validation
    assert diagnostic.payload.module == :"Cure.Demo"
    assert diagnostic.payload.file == "demo.cure"
    refute rendered =~ ":final_core_violation"
    refute rendered =~ "{:hole"
  end

  test "codegen rejection families retain a stable public explanation" do
    rendered = Host.render({:unsupported_container, :protocol}, "demo.cure")
    assert rendered =~ "UNSUPPORTED CONTAINER"
    assert rendered =~ "protocol"
    refute rendered =~ "codegen error"
  end

  test "converts legacy type and edition tuples into structured diagnostics" do
    type_rendered = Host.render({:type_mismatch, "expected Int, found String", [line: 1, col: 20]}, "demo.cure")
    assert type_rendered =~ "[E093]"

    edition_rendered = Host.render({:edition_pragma_malformed, 1, 1}, "demo.cure")
    assert edition_rendered =~ "[E094]"
    assert edition_rendered =~ "EDITION PRAGMA IS MALFORMED"

    contextual =
      Cure.Compiler.Errors.format_with_source(
        {:edition_error, {:unknown_edition, "9999"}},
        "demo.cure",
        "@edition(\"9999\")\n"
      )

    assert contextual =~ "[E094]"
    assert contextual =~ "9999"
    refute contextual =~ "| @edition"
  end

  test "keeps macro validation failures structured at the host boundary" do
    rendered = Host.render({:rule_unpinned, ["every"]}, "macro.cure")

    assert rendered =~ "[E092]"
    assert rendered =~ "MACRO RULE NEEDS A WORKED EXAMPLE"
    assert rendered =~ "every"
    refute rendered =~ ":rule_unpinned"
  end

  test "keeps macro expansion cycles and budgets structured with provenance" do
    cycle =
      Host.render(
        {:macro_expansion_cycle, [%{keyword: "outer", line: 3, col: 5}]},
        "macro.cure"
      )

    budget =
      Host.render(
        {:macro_expansion_budget, :expansion_count, [%{keyword: "outer", line: 3, col: 5}]},
        "macro.cure"
      )

    assert cycle =~ "[E092]"
    assert cycle =~ "recursive"
    assert budget =~ "[E092]"
    assert budget =~ "expansion_count"
    refute cycle =~ ":macro_expansion_cycle"
    refute budget =~ ":macro_expansion_budget"
  end

  test "renders erasure violations with the supported runtime classes" do
    rendered = Host.render({:unknown_erasure_class, :Handle, :banana}, "demo.cure")

    assert rendered =~ "[E102]"
    assert rendered =~ "banana"
    assert rendered =~ "pid"
    refute rendered =~ ":unknown_erasure_class"
  end

  test "renders trusted positivity and relevance rejections" do
    positivity = Host.render({:non_strictly_positive, :Bad}, "demo.cure")
    assert positivity =~ "[E103]"
    assert positivity =~ "Bad"

    relevance = Host.render({:erased_used_relevantly, %{binder: 0, site: :returned}}, "demo.cure")
    assert relevance =~ "[E104]"
    assert relevance =~ "function's runtime result"
    refute relevance =~ "``"
  end

  test "renders ambiguous proof search with proof-specific context" do
    rendered =
      Host.render(
        {:ambiguous_proof_search, {:global, :Goal}, [{:lemma, :first}, {:lemma, :second}]},
        "proof.cure"
      )

    assert rendered =~ "[E026]"
    assert rendered =~ "AMBIGUOUS"
    refute rendered =~ ":ambiguous_proof_search"
  end

  test "renders restricted resource usage violations through the trusted diagnostic family" do
    rendered =
      Host.render(
        {:usage_violation, %{binder: 0, declared: :linear, used: :unrestricted}},
        "demo.cure"
      )

    assert rendered =~ "[E117]"
    assert rendered =~ "linear"
    assert rendered =~ "may consume it"
    assert rendered =~ "number of times"
    refute rendered =~ "this binding"
    refute rendered =~ ":usage_violation"
  end

  test "renders missing interface instances with contextual type information" do
    rendered =
      Host.render(
        {:source_context, {:no_instance, :Comparable, {:rigid, 0}}, %{expectation_origin: :call_argument}},
        "demo.cure"
      )

    assert rendered =~ "[E093]"
    assert rendered =~ "NO `COMPARABLE` IMPLEMENTATION FOUND"
    assert rendered =~ "Comparable"
    assert rendered =~ "type variable"
    assert rendered =~ "where Comparable(...)"
    refute rendered =~ "{:rigid, 0}"
    refute rendered =~ ":no_instance"
  end

  test "renders named-instance and coherence failures through shared diagnostics" do
    named = Host.render({:source_context, {:no_named_instance, :strictInt}, %{}}, "demo.cure")
    overlap = Host.render({:overlapping_instance, :Comparable, :Int}, "demo.cure")

    assert named =~ "[E011]"
    assert named =~ "strictInt"
    refute named =~ ":no_named_instance"
    assert overlap =~ "[E105]"
    assert overlap =~ "Comparable"
    assert overlap =~ "Int"
    refute overlap =~ ":overlapping_instance"
  end

  test "renders record projection failures with record-field identity" do
    unknown = Host.render({:unknown_field, :Point, :colour}, "demo.cure")
    non_record = Host.render({:source_context, {:projection_non_record, :x}, %{}}, "demo.cure")

    assert unknown =~ "[E091]"
    assert unknown =~ "Point.colour"
    assert non_record =~ "[E093]"
    assert non_record =~ "`x`"
    refute unknown =~ ":unknown_field"
    refute non_record =~ ":projection_non_record"
  end

  test "record-field suggestions come from the actual record shape" do
    diagnostic =
      Cure.Diagnostic.Adapter.from_error({:unknown_field, :Point, "colour", [:x, :y, :color]})

    assert diagnostic.payload.record == :Point
    assert Enum.map(diagnostic.payload.candidates, & &1) == ["color"]
    assert hd(diagnostic.suggestions).message == "Did you mean `color`?"
  end

  test "filters name suggestions semantically before edit-distance ranking" do
    diagnostic =
      Cure.Diagnostic.Adapter.unknown_name(:value, "pritn",
        candidates: [
          %{id: :private_print, name: "print", namespace: :value, visibility: :private},
          %{id: :wrong_ns, name: "pritn", namespace: :type, visibility: :public},
          %{id: :wrong_arity, name: "print", namespace: :value, arity: 2},
          %{id: :qualified, name: "print", namespace: :value, owner: "Std.Io", imported: false},
          %{id: :usable, name: "println", namespace: :value, visibility: :public, arity: 1}
        ],
        arity: 1
      )

    assert diagnostic.payload.candidate_details |> Enum.map(& &1.candidate_id) == [:usable, :qualified]

    assert diagnostic.suggestions == [
             %Cure.Diagnostic.Suggestion{
               message: "Did you mean `println`, `Std.Io.print`? Qualify it or import its module.",
               applicability: :maybe_incorrect
             }
           ]
  end

  test "renders operator type failures with operator-specific context" do
    operand = Host.render({:unsupported_operand_type, :+}, "demo.cure")
    meaning = Host.render({:no_operator_meaning, :<<<}, "demo.cure")

    assert operand =~ "[E093]"
    assert operand =~ "`+` DOES NOT SUPPORT THESE OPERANDS"
    assert operand =~ "`+`"
    assert meaning =~ "[E093]"
    assert meaning =~ "`<<<` HAS NO DEFINITION"
    assert meaning =~ "<<<"
    refute operand =~ ":unsupported_operand_type"
    refute meaning =~ ":no_operator_meaning"
  end

  test "renders inference failures with actionable contextual type guidance" do
    match = Host.render({:cannot_infer_match_type, {:match, :branches}}, "demo.cure")
    lambda = Host.render({:lambda_expected_pi, {:global, :Int}}, "demo.cure")

    assert match =~ "[E093]"
    assert match =~ "CANNOT INFER MATCH TYPE"
    assert match =~ "Add a result annotation"
    assert lambda =~ "[E093]"
    assert lambda =~ "LAMBDA NEEDS A FUNCTION TYPE"
    assert lambda =~ "Int"
    refute match =~ ":cannot_infer_match_type"
    refute lambda =~ ":lambda_expected_pi"
  end

  test "renders pattern coverage failures with branch identity" do
    missing = Host.render({:source_context, {:missing_branch, :None}, %{}}, "match.cure")
    impossible = Host.render({:source_context, {:reachable_impossible, :Some}, %{}}, "match.cure")
    duplicate = Host.render({:source_context, {:duplicate_branch, :Some}, %{}}, "match.cure")

    assert missing =~ "[E118]"
    assert missing =~ "PATTERN MATCH IS MISSING `NONE`"
    assert missing =~ "None"
    assert impossible =~ "[E118]"
    assert impossible =~ "`SOME` IS REACHABLE HERE"
    assert duplicate =~ "[E118]"
    assert duplicate =~ "`SOME` HAS MORE THAN ONE BRANCH"
    refute missing =~ ":missing_branch"
    refute impossible =~ ":reachable_impossible"
    refute duplicate =~ ":duplicate_branch"
  end

  test "renders forced and rematched pattern failures contextually" do
    forced = Host.render({:source_context, {:forced_pattern_mismatch, :Int, :String}, %{}}, "pattern.cure")

    rematch =
      Host.render(
        {:source_context, {:with_rematch_ctor_mismatch, :Some, :None}, %{}},
        "pattern.cure"
      )

    named = Host.render({:source_context, {:named_implicit_unforced, :value}, %{}}, "pattern.cure")

    assert forced =~ "[E093]"
    assert forced =~ "FORCED PATTERN DOES NOT MATCH"
    assert rematch =~ "[E093]"
    assert rematch =~ "WITH REMATCH CONSTRUCTOR MISMATCH"
    assert named =~ "[E011]"
    assert named =~ "value"
    refute forced =~ ":forced_pattern_mismatch"
    refute rematch =~ ":with_rematch_ctor_mismatch"
    refute named =~ ":named_implicit_unforced"
  end

  test "renders kernel rejection paths as contextual type diagnostics" do
    index = Host.render({:source_context, {:index_mismatch, :different_index}, %{}}, "kernel.cure")
    escaping = Host.render({:source_context, {:escaping_variable, 3}, %{}}, "kernel.cure")

    assert index =~ "[E093]"
    assert index =~ "DEPENDENT INDEX MISMATCH"
    assert escaping =~ "[E093]"
    assert escaping =~ "TYPE VARIABLE ESCAPES ITS SCOPE"
    refute index =~ ":index_mismatch"
    refute escaping =~ ":escaping_variable"
  end

  test "renders invalid macro families as authored macro diagnostics" do
    rendered =
      Host.render(
        {:invalid_macro_family,
         %{reason: {:syntax_family_cycle, ["First", "Second", "First"]}, related_spans: [], line: 4, column: 1}},
        "macro.cure"
      )

    assert rendered =~ "[E092]"
    assert rendered =~ "SYNTAX FAMILIES FORM A CYCLE"
    assert rendered =~ "First → Second → First"
    refute rendered =~ ":invalid_macro_family"
  end

  test "renders interface implementation failures with declaration context" do
    unknown = Host.render({:no_such_interface, :Missing}, "impl.cure")
    method = Host.render({:unknown_interface_method, :Eq, :compare}, "impl.cure")
    missing = Host.render({:missing_method, :Eq, :compare}, "impl.cure")
    mismatch = Host.render({:method_signature_mismatch, :Eq, :compare}, "impl.cure")
    superinterface = Host.render({:missing_superinterface, :Ord, :Eq, :Int}, "impl.cure")

    assert unknown =~ "[E091]"
    assert unknown =~ "UNKNOWN INTERFACE"
    assert method =~ "[E091]"
    assert method =~ "compare"
    assert missing =~ "[E105]"
    assert missing =~ "INTERFACE METHOD IS MISSING"
    assert mismatch =~ "[E105]"
    assert mismatch =~ "SIGNATURE MISMATCH"
    assert superinterface =~ "[E105]"
    assert superinterface =~ "REQUIRED SUPERINTERFACE IS MISSING"

    for output <- [unknown, method, missing, mismatch, superinterface] do
      refute output =~ ":no_such_interface"
      refute output =~ ":missing_method"
    end
  end

  test "renders union declaration collisions as actionable diagnostics" do
    ground = Host.render({:union_member_not_ground, {:var, "T"}}, "union.cure")
    shape = Host.render({:unsupported_member_shape, [:Map]}, "union.cure")
    runtime = Host.render({:same_runtime_shape, ["A", "B"]}, "union.cure")
    literal = Host.render({:same_erased_literal, [1, 1]}, "union.cure")

    assert ground =~ "[E105]"
    assert ground =~ "UNION MEMBER IS NOT GROUND"
    assert shape =~ "UNSUPPORTED UNION MEMBER SHAPE"
    assert runtime =~ "SAME RUNTIME SHAPE"
    assert literal =~ "SAME ERASED LITERAL"

    for output <- [ground, shape, runtime, literal] do
      refute output =~ ":same_runtime_shape"
      refute output =~ ":same_erased_literal"
    end
  end

  test "renders deriving and stdlib source failures without internal errors" do
    derive = Host.render({:cannot_derive, :Show}, "derive.cure")
    constraints = Host.render({:deriving_needs_constraints, :BeamDecode, :Packet}, "derive.cure")
    method = Host.render({:cannot_derive_method, :Show, :show, :unsupported}, "derive.cure")
    missing = Host.render({:missing_stdlib_source, "Std.Missing", "/tmp/Std/Missing.cure"}, "derive.cure")

    assert derive =~ "[E105]"
    assert derive =~ "CANNOT DERIVE INTERFACE"
    assert constraints =~ "CANNOT DERIVE `BEAMDECODE` FOR `PACKET`"
    assert method =~ "CANNOT DERIVE INTERFACE METHOD"
    assert missing =~ "[E095]"
    assert missing =~ "Cannot read"
    refute derive =~ ":cannot_derive"
    refute missing =~ ":missing_stdlib_source"
  end

  test "renders overload, projection, and unresolved-index failures contextually" do
    overload = Host.render({:no_matching_overload, :map, [:Int, :String]}, "types.cure")
    ambiguous = Host.render({:ambiguous_overload, :map, ["List.map/2", "Seq.map/2"]}, "types.cure")
    projection = Host.render({:projection_not_a_record, :Int}, "types.cure")
    pattern = Host.render({:typed_pattern_arity, 2}, "types.cure")
    index = Host.render({:unsolved_index, :VCons}, "types.cure")
    occurs = Host.render({:occurs_check, 1, {:var, 1}}, "types.cure")

    assert overload =~ "[E093]"
    assert overload =~ "NO OVERLOAD OF `MAP` MATCHES"
    assert overload =~ "Int, String"
    assert ambiguous =~ "CALL TO `MAP` IS AMBIGUOUS"
    assert ambiguous =~ "List.map/2"
    assert ambiguous =~ "Seq.map/2"
    assert projection =~ "RECORD PROJECTION REQUIRES A RECORD"
    assert pattern =~ "[E003]"
    assert index =~ "UNRESOLVED INDEX"
    assert occurs =~ "[E093]"
    assert occurs =~ "INFINITE TYPE DETECTED"
  end

  test "renders ordinary unsupported elaboration forms without E101" do
    expression = Host.render({:unsupported_expression, :effectful_value}, "forms.cure")
    annotation = Host.render({:let_needs_annotation, :value}, "forms.cure")
    pattern = Host.render({:nonlinear_pattern, :x}, "forms.cure")
    alias_error = Host.render({:typealias_not_a_type, :value}, "forms.cure")
    effect = Host.render({:effect_arity, :send, 2, 1}, "forms.cure")

    assert expression =~ "UNSUPPORTED EXPRESSION"
    assert annotation =~ "BINDING NEEDS AN ANNOTATION"
    assert pattern =~ "[E119]"
    assert pattern =~ "PATTERN BINDS `X` MORE THAN ONCE"
    assert alias_error =~ "TYPE ALIAS DOES NOT NAME A TYPE"
    assert effect =~ "EFFECT OPERATION ARITY MISMATCH"

    for output <- [expression, annotation, alias_error, effect] do
      assert output =~ "[E093]"
      refute output =~ "INTERNAL COMPILER ERROR"
    end

    refute pattern =~ "INTERNAL COMPILER ERROR"
  end

  test "locationless name and module errors do not blame the start of an unrelated source" do
    source = "mod Unrelated\n  fn complete() -> Int = 1\nend\n"

    for reason <- [
          {:ambiguous_name, :shared, ["Left", "Right"]},
          {:duplicate_module, "Repeated", ["one.cure", "two.cure"]}
        ] do
      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "unrelated.cure", source)
      assert diagnostic.primary == nil
      refute Cure.Diagnostic.Renderer.plain(diagnostic, registry) =~ "1 | mod Unrelated"
    end
  end

  test "bare branch verdicts do not fall back to generic elaboration failure" do
    rendered = Host.render(:branch_type, "branches.cure")

    assert rendered =~ "PATTERN BRANCHES DISAGREE"
    refute rendered =~ "ELABORATION FAILED"
  end

  test "bare trusted verdicts retain actionable type-checking titles" do
    assert Host.render(:branch_arity, "patterns.cure") =~ "PATTERN BRANCH HAS THE WRONG ARITY"
    assert Host.render(:coverage, "patterns.cure") =~ "PATTERN MATCH IS NOT EXHAUSTIVE"
    assert Host.render(:index_arity, "types.cure") =~ "INDEXED TYPE HAS THE WRONG ARITY"
  end

  test "renders declaration conflicts with their authored identity" do
    rendered = Host.render({:overlapping_overload, :move, 1}, "demo.cure")

    assert rendered =~ "[E105]"
    assert rendered =~ "move"
    assert rendered =~ "arity 1"
  end

  test "renders extern target-arity conflicts through contextual arity diagnostics" do
    rendered =
      Host.render(
        {:extern_arity_mismatch, :head, 2, 1},
        "extern.cure"
      )

    assert rendered =~ "[E003]"
    assert rendered =~ "head"
    assert rendered =~ "declares target arity 2"
    assert rendered =~ "present Cure arity is 1"
    refute rendered =~ ":extern_arity_mismatch"
  end

  test "renders constructor and tuple pattern arity failures as structured diagnostics" do
    constructor = Host.render({:constructor_arity_mismatch, :Some}, "pattern.cure")
    tuple = Host.render({:tuple_arity_mismatch, :too_many, {:tuple, 3}}, "pattern.cure")

    assert constructor =~ "[E003]"
    assert constructor =~ "Some"
    assert tuple =~ "[E003]"
    assert tuple =~ "too_many"
    refute constructor =~ ":constructor_arity_mismatch"
    refute tuple =~ ":tuple_arity_mismatch"
  end

  test "renders typed-pattern and with-rematch failures contextually" do
    pattern = Host.render({:typed_pattern_type_mismatch, {:named, "Int"}}, "pattern.cure")
    rematch = Host.render({:with_rematch_arity_mismatch, 2, 1}, "pattern.cure")

    assert pattern =~ "[E093]"
    assert pattern =~ "PATTERN ANNOTATION DOES NOT MATCH"
    assert rematch =~ "[E003]"
    assert rematch =~ "2 pattern(s)"
    refute pattern =~ ":typed_pattern_type_mismatch"
    refute rematch =~ ":with_rematch_arity_mismatch"
  end

  test "renders unsupported async and quote-boundary failures" do
    async = Host.render({:unsupported_async, "async primitive is unavailable", [line: 2]}, "demo.cure")
    assert async =~ "[E107]"
    assert async =~ "async primitive is unavailable"

    splice = Host.render({:splice_outside_quote, :splice, [line: 2]}, "demo.cure")
    assert splice =~ "[E108]"
    assert splice =~ "quote"
  end

  test "renders dependency resolution branches as operational diagnostics" do
    invalid = Host.render({:invalid_dependency, "bad"}, "Cure.toml")
    missing = Host.render({:no_versions, "json"}, "Cure.toml")
    edition = Host.render({:dependency_edition_error, "dep", {:unknown_edition, "9999"}}, "Cure.toml")

    assert invalid =~ "[E097]"
    assert invalid =~ "bad"
    assert missing =~ "[E097]"
    assert missing =~ "json"
    assert edition =~ "[E097]"
    assert edition =~ "dep"
    refute invalid =~ ":invalid_dependency"
    refute edition =~ ":dependency_edition_error"
  end

  test "recognizes project, registry, transparency, watch, and resource failures at the host boundary" do
    cases = [
      {{:unknown_watch_action, :explode}, "E098"},
      {{:file_error, :enoent}, "E098"},
      {{:decode_failed, :invalid_json}, "E098"},
      {{:parse, :invalid_lock}, "E098"},
      {{:fetch_failed, "registry.json", :timeout}, "E038"},
      {{:hash_mismatch, "Demo@1.0.0"}, "E039"},
      {{:package_not_found, "Demo"}, "E040"},
      {{:unreachable, :econnrefused}, "E042"},
      {{:chain_broken, 3}, "E042"},
      {{:app_resource_write_failed, "priv/app.json", :eacces}, "E096"}
    ]

    for {reason, expected_code} <- cases do
      rendered = Cure.Diagnostic.Host.render(reason, "project.cure", "")
      assert rendered =~ "[#{expected_code}]", "#{inspect(reason)} was not operationally classified"
      refute rendered =~ "INTERNAL COMPILER ERROR"
    end
  end

  test "renders project application validation failures as artifact diagnostics" do
    duplicate = Host.render({:duplicate_app, [{"one.cure", "One"}, {"two.cure", "Two"}]}, "Cure.toml")
    mismatch = Host.render({:app_name_mismatch, "Expected", "Actual"}, "Cure.toml")

    assert duplicate =~ "[E100]"
    assert duplicate =~ "more than one application"
    assert mismatch =~ "[E100]"
    assert mismatch =~ "Expected"
    assert mismatch =~ "Actual"
    refute duplicate =~ ":duplicate_app"
    refute mismatch =~ ":app_name_mismatch"
  end

  test "preserves the inner diagnostic through project compile-failure envelopes" do
    rendered =
      Host.render(
        {:compile_failed, {:extern_arity_mismatch, :head, 2, 1}},
        "Cure.toml"
      )

    assert rendered =~ "[E003]"
    assert rendered =~ "head"
    refute rendered =~ ":compile_failed"
  end

  test "renders release operational failures through shared diagnostics" do
    build = Host.render({:release_build_failed, :systools}, "release.cure")
    app = Host.render({:release_app_missing, :demo, :missing_app_file}, "release.cure")
    config = Host.render({:sys_config_read_failed, "sys.config", :enoent}, "release.cure")

    assert build =~ "[E098]"
    assert build =~ "Release script generation failed"
    assert app =~ "[E100]"
    assert app =~ "demo"
    assert config =~ "[E095]"
    assert config =~ "sys.config"
    refute build =~ ":release_build_failed"
  end

  test "converts aggregate type errors through the contextual type family" do
    rendered =
      Host.render(
        {:type_error, [{:type_mismatch, "expected Int, found String", [line: 1, col: 1]}]},
        "demo.cure"
      )

    assert rendered =~ "[E093]"
    assert rendered =~ "expected Int, found String"

    assert Cure.Compiler.Errors.format_with_source(
             {:type_error, [{:type_mismatch, "expected Int, found String", [line: 1, col: 1]}]},
             "demo.cure",
             "fn run() -> Int = 1\n"
           ) =~ "[E093]"
  end

  test "does not fall through to legacy formatting for an unregistered reason" do
    rendered = Host.render({:unregistered_compiler_reason, :detail}, "demo.cure")

    assert rendered =~ "[E101]"
    assert rendered =~ "fingerprint"
    assert rendered =~ "unregistered_compiler_reason"
    assert rendered =~ "detail"
  end

  test "an unregistered source-context reason retains the failing declaration and type evidence" do
    reason =
      {:source_context, {:index_mismatch, {:global, :left}, {:global, :right}},
       %{
         checking: :"Std.Regex#compile_pattern",
         expected_type: {:global, :Expected},
         inferred_type: {:global, :Inferred},
         core_term: {:global, :offending_state}
       }}

    {diagnostic, _registry} = Host.to_diagnostic(reason, "lib/std_deps/regex/regex.cure")
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, nil, width: 100)

    assert diagnostic.code == "E101"
    assert diagnostic.payload.declaration == :"Std.Regex#compile_pattern"
    assert diagnostic.payload.expected_type =~ "Expected"
    assert diagnostic.payload.inferred_type =~ "Inferred"
    assert diagnostic.payload.core_term =~ "offending_state"
    assert diagnostic.payload.impossible_shape =~ "index_mismatch"
    assert rendered =~ "Std.Regex#compile_pattern"
    assert rendered =~ "index_mismatch"
  end

  test "canonical interface registration renders non-uniform parameters as an actionable source error" do
    reason =
      {:module_interface_registration_failed, {"root", "Std.Bounded"},
       {:non_uniform_parameter, %{position: 0, family: :"Std.Bounded#BoundedSum", ctor: :BoundedLeft}}}

    {diagnostic, registry} = Host.to_diagnostic(reason, "lib/std/bounded.cure")
    rendered = Cure.Diagnostic.Renderer.plain(diagnostic, registry, width: 100)

    refute diagnostic.code == "E101"
    assert rendered =~ "CONSTRUCTOR CHANGES A TYPE PARAMETER"
    assert rendered =~ "BoundedSum"
    assert rendered =~ "BoundedLeft"
    assert rendered =~ "values that vary belong in"
    assert rendered =~ "the `indices` telescope"
    assert diagnostic.payload.pipeline_stage == :interface_registration
    assert diagnostic.payload.module_identity == {"root", "Std.Bounded"}
  end
end
