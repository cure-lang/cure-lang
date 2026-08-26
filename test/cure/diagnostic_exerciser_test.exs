defmodule Cure.DiagnosticExerciserTest do
  use ExUnit.Case, async: false

  alias Cure.Diagnostic.{Operational, Renderer}

  defp render_options do
    config = Application.get_env(:cure, :diagnostics_exerciser, [])
    [color: Keyword.get(config, :color, :always), width: Keyword.get(config, :width, 80)]
  end

  test "exercises every public diagnostic family and shows user output" do
    compiler_cases = [
      {"unknown global", "E091", "mod DiagnosticUnknown\n  fn run() -> Int = missing_name\n", :unknown_name_resolution},
      {"syntax error", "E094", "mod DiagnosticSyntax\n  fn run(] -> Int = 1\n", :syntax_error_parser},
      {"lexer syntax error", "E094", "mod DiagnosticLexer\n  fn run() -> String = \"not closed\n", :syntax_error_lexer},
      {"type mismatch", "E093",
       "mod DiagnosticType\n  type Nat = Z | S(Nat)\n  fn bad() -> Equivalent(Nat, Z, S(Z)) = reflexive(Z)\n",
       :type_mismatch_elaboration},
      {"unfilled hole", "E014", "mod DiagnosticHole\n  fn bad() -> Int = ???\n", :unfilled_hole},
      {"implementation member scope", "E116",
       "mod DiagnosticImplementation\n  interface Marker(t)\n    fn mark(value: t) -> Bool\n  implementation Marker for Int\n  fn mark(value: Int) -> Bool = true\nend\n",
       :implementation_scope},
      {"unterminated lambda", "E035", "fn (x) -> x; x;", :unterminated_lambda},
      {"unrecognized pattern", "E090",
       "mod DiagnosticPattern\n  fn bad(x: Int) -> Int = match x\n    1..10 -> 1\n    _ -> 0\n",
       :unrecognized_pattern_elaboration},
      {"missing implicit", "E011", "mod DiagnosticImplicit\n  fn bad() -> Int = reflexive()\n", :missing_implicit},
      {"unknown pattern constructor", "E091",
       "mod DiagnosticCtor\n  type Nat = Z | S(Nat)\n  fn bad(x: Nat) -> Nat = match x\n    Missing() -> Z\n    _ -> Z\n",
       :unknown_pattern_name},
      {"pickup without else", "E076", "mod DiagnosticPickupNoElse\n  fn bad(x: Int) -> Int = pickup\n    x > 0 -> 1\n",
       :pickup_missing_else},
      {"pickup else not last", "E077",
       "mod DiagnosticPickupElseLast\n  fn bad(x: Int) -> Int = pickup\n    else -> 1\n    x > 0 -> 2\n",
       :pickup_else_not_last},
      {"pickup multiple else", "E078",
       "mod DiagnosticPickupMultipleElse\n  fn bad(x: Int) -> Int = pickup\n    else -> 1\n    else -> 2\n",
       :pickup_multiple_else},
      {"record field mismatch", "E022",
       "mod DiagnosticRecord\n  type Nat = Z | S(Nat)\n  rec Point\n    x: Nat\n    y: Nat\n  fn bad() -> Point = Point{x: S(Z()), z: Z()}\nend\n",
       :record_field_mismatch},
      {"extern untyped head", "E056",
       "mod DiagnosticExternUntyped\n  @extern(:erlang, :hd, 1)\n  fn head(xs) -> Int\nend\n", :extern_untyped_head},
      {"extern has body", "E057",
       "mod DiagnosticExternBody\n  @extern(:erlang, :self, 0)\n  fn me() -> Atom = :oops\nend\n", :extern_has_body},
      {"unsupported spawn", "E107", "mod DiagnosticSpawn\n  fn bad() -> Int = spawn 1\nend\n", :unsupported_async},
      {"call arity mismatch", "E003",
       "mod DiagnosticArity\n  fn id(value: Int) -> Int = value\n  fn bad() -> Int = id()\nend\n",
       :arity_mismatch_elaboration},
      {"unknown record", "E021", "mod DiagnosticUnknownRecord\n  fn bad() = Missing{value: 1}\nend\n", :unknown_record},
      {"splice outside quote", "E108",
       "mod DiagnosticSplice\n  use Std.Syntax\n  fn bad(value: Syntax) -> Syntax = consume($(value))\nend\n",
       :splice_outside_quote},
      {"named argument mismatch", "E115",
       "mod DiagnosticNamedArgument\n  fn pair(left: Int, right: Int) -> Int = left\n  fn bad() -> Int = pair(left: 1, 2)\nend\n",
       :named_argument_mismatch},
      {"proof chain mismatch", "E110",
       "mod DiagnosticProofMismatch\n  use Std.Equivalent\n  fn proof(x: Int) -> Equivalent(Int, x, x) = proof chain\n    x\n      == 1\n      because reflexive(x)\nend\n",
       :proof_chain_mismatch},
      {"directed rewrite failure", "E111",
       "mod DiagnosticRewrite\n  use Std.Equivalent\n  fn proof(x: Int, y: Int, equality: Equivalent(Int, x, y)) -> Equivalent(Int, x, x) = proof chain\n    x\n      == x\n      because\n        rewrite using equality\n        equality\nend\n",
       :rewrite_failed},
      {"simplification failure", "E112",
       "mod DiagnosticSimplify\n  type Nat = Z | S(Nat)\n  fn bad(x: Nat) -> Equivalent(Nat, x, S(x)) = proof chain\n    x == S(x)\n    because simplify\nend\n",
       :simplification_failed},
      {"induction failure", "E113",
       "mod DiagnosticInduction\n  type Nat = Z | S(Nat)\n  fn bad(value: Nat) -> Equivalent(Nat, value, value) = induction value\n    case Z => reflexive(Z)\n    case S() => reflexive(Z)\nend\n",
       :induction_failed},
      {"defining equation unavailable", "E114",
       "mod DiagnosticEquation\n  type Bit = Off | On\n  fn flip(bit: Bit) -> Bit = match bit\n    Off -> On\n    On -> Off\n  fn bad() = flip.Missing\nend\n",
       :defining_equation_unavailable},
      {"erasure declaration", "E102", "mod DiagnosticErasure\n  @erases(:banana)\n  opaque type Handle\nend\n",
       :erasure_violation},
      {"relevant use of erased value", "E104",
       "mod DiagnosticRelevance\n  type Nat = Z | S(Nat)\n  type SNat indices (n: Nat)\n    szero : SNat(Z)\n    ssuc : SNat(n) -> SNat(S(n))\n  type NV indices (n: Nat)\n    vz : NV(Z)\n    vs : SNat(n) -> NV(S(n))\n  fn bad({n: Nat}, value: NV(n)) -> Nat = n\nend\n",
       :erased_value_used_relevantly},
      {"resource usage violation", "E117",
       "mod DiagnosticUsage\n  fn consume(value: Int) -> Int = value\n  fn bad(@linear value : Int) -> Int = consume(value)\nend\n",
       :resource_usage_violation},
      {"pattern coverage", "E118",
       "mod DiagnosticCoverage\n  type Choice = First | Second\n  fn choose(value: Choice) -> Choice = match value\n    First() -> First()\nend\n",
       :pattern_coverage},
      {"pattern structure", "E119",
       "mod DiagnosticPatternStructure\n  use Std.Binary\n  fn first(value: Binary) -> Int = match value\n    <<byte, _rest::binary>> -> byte\nend\n",
       :pattern_structure},
      {"primitive declaration", "E120", "mod DiagnosticPrimitive\n  @builtin(:sparkle) primitive Sparkle\nend\n",
       :primitive_declaration},
      {"non-positive recursive type", "E103",
       "mod DiagnosticPositivity\n  type Nat = Z | S(Nat)\n  type Bad = MkBad((Bad) -> Nat)\nend\n",
       :non_strictly_positive_type},
      {"type-level function is not total", "E013",
       "mod DiagnosticTotality\n  type Dec = Dcoupled | Causal\n  type Sig = CSig | ESig\n  type SVDesc = SVNil | SVCons(Sig, SVDesc)\n  fn andd(x: Dec, y: Dec) -> Dec = andd(x, y)\n  type SF indices (as: SVDesc, bs: SVDesc, d: Dec)\n    prim : SF(as, bs, Causal)\n    seq : SF(as, bs, d1) -> SF(bs, cs, d2) -> SF(as, cs, andd(d1, d2))\nend\n",
       :totality_failure},
      {"duplicate parameter", "E105", "mod DiagnosticDuplicate\n  fn bad(value: Int, value: Int) -> Int = value\nend\n",
       :declaration_conflict_elaboration},
      {"sibling module collision", "E105",
       "mod DiagnosticLeft\n  fn shared(value: Int) -> Int = value\nend\nmod DiagnosticRight\n  fn shared(value: Int) -> Int = value\nend\n",
       :declaration_conflict_name_resolution},
      {"parser macro failure", "E092", "macro M\n  syntax m <x: X> where Eq(y) becomes x\n", :parser_macro_failure},
      {"macro expansion failure", "E092",
       "mod DiagnosticExpansion\n  use Std.Syntax\n  use Std.Syntax.Raw\n  macro Bad\n    syntax bad computed by build\n  fn build(input: Syntax) -> Syntax = unsafe_raw(SInt(1))\n  fn result() -> Int = bad\nend\n",
       :macro_expansion_failure},
      {"parser operator conflict", "E106", "mod DiagnosticFixity\n  use Std.Operators\n  infix `|>` : Additive\nend\n",
       :operator_conflict_parser},
      {"proof chain syntax", "E109", "proof chain\n  first\n", :proof_chain_syntax},
      {"proof container shape", "E026", "proof InvalidProof\n  fn bad() -> Int = 1\n", :proof_shape_mismatch}
    ]

    boundary_cases = [
      {"arity mismatch", "E003", {:arity_mismatch, "expected 2 arguments", [line: 1, col: 17]}},
      {"extern untyped head", "E056", {:extern_untyped_head, "parameter is untyped", [line: 1, col: 1]}},
      {"extern has body", "E057", {:extern_has_body, "body is not allowed", [line: 1, col: 1]}},
      {"unknown record", "E021", {:unknown_record, :Missing}},
      {"proof shape mismatch", "E026", {:proof_shape_mismatch, "not a proof", "bad"}},
      {"totality failure", "E013", {:totality_required, :loop}},
      {"pickup without else", "E076", {:pickup_no_else, "missing else", [line: 1, col: 1]}},
      {"pickup else not last", "E077", {:pickup_else_not_last, "else is not last", [line: 1, col: 1]}},
      {"pickup multiple else", "E078", {:pickup_multiple_else, "multiple else", [line: 1, col: 1]}},
      {"duplicate module", "E087", {:duplicate_module_identity, "Demo", "a.cure", "b.cure"}},
      {"ambiguous name", "E089", {:ambiguous_name, :helper, ["Demo.A", "Demo.B"]}},
      {"import cycle", "W086", {:import_cycle, [%{module: "Demo.A", path: "a.cure", line: 1}]}},
      {"macro expansion", "E092",
       {:lift_module_error,
        %{module: "Demo.Generated", cause: {:unknown_global, :missing}, source_provenance: %{macro: :spawn}}}},
      {"erasure violation", "E102", {:unknown_erasure_class, :Handle, :banana}},
      {"positivity rejection", "E103", {:non_strictly_positive, :Bad}},
      {"relevance rejection", "E104", {:erased_used_relevantly, %{binder: 0, site: :returned}}},
      {"declaration conflict", "E105", {:duplicate_type, :Widget}},
      {"missing interface", "E091", {:no_such_interface, :Missing}},
      {"missing interface method", "E105", {:missing_method, :Eq, :compare}},
      {"union runtime collision", "E105", {:same_runtime_shape, [:Left, :Right]}},
      {"deriving failure", "E105", {:cannot_derive, :Show}},
      {"kernel index mismatch", "E093", {:index_mismatch, :different_index}},
      {"kernel inference hole", "E014", {:hole_in_inference_position, "h"}},
      {"constructor needs checking", "E093", {:ctor_requires_checking_mode, :Nat}},
      {"non-concrete bound", "E093", {:bounded_bound_not_concrete, {:var, 0}}},
      {"cyclic type aliases", "E105", {:cyclic_typealiases, ["A", "B", "A"]}},
      {"module identity missing", "E095", {:module_identity_missing, "demo.cure"}},
      {"character bound missing", "E093", {:char_literal_needs_bounded, 97}},
      {"character range failure", "E093", {:char_literal_out_of_range, 0x110000}},
      {"extern returns union", "E093", {:extern_returns_union, :foreign, {:union, []}}},
      {"dependent match inference", "E093", {:cannot_infer_dependent_match, :branch}},
      {"unbound kernel variable", "E091", {:unbound_var, :missing}},
      {"unknown type family", "E091", {:unknown_family, :Missing}},
      {"unknown constructor", "E091", {:unknown_ctor, :Missing}},
      {"foreign constructor", "E091", {:foreign_ctor, :Missing}},
      {"missing primitive builtin", "E120", {:primitive_missing_builtin, :Int}},
      {"unknown primitive tag", "E120", {:unknown_primitive_tag, :future_primitive}},
      {"primitive floor mismatch", "E120", {:primitive_floor_mismatch, :Binary, {:float_type}, {:binary_type}}},
      {"unsupported declaration", "E120", {:unsupported_declaration, :future_declaration}},
      {"generated hole validation", "E092", {:generated_hole_not_well_typed, :term}},
      {"duplicate macro unit", "E092", {:duplicate_unit, "ms"}},
      {"overload has no match", "E093", {:no_matching_overload, :map, [:Int, :String]}},
      {"projection is not a record", "E093", {:projection_not_a_record, :Int}},
      {"typed pattern arity", "E003", {:typed_pattern_arity, 2}},
      {"unsupported expression", "E093", {:unsupported_expression, :unknown_form}},
      {"occurs check", "E093", {:occurs_check, 1, {:var, 1}}},
      {"forced pattern mismatch", "E093", {:source_context, {:forced_pattern_mismatch, :Int, :String}, %{}}},
      {"macro family failure", "E092",
       {:invalid_macro_family,
        %{reason: {:syntax_family_cycle, ["A", "B", "A"]}, related_spans: [], line: 1, column: 1}}},
      {"missing stdlib source", "E095", {:missing_stdlib_source, "Std.Missing", "/tmp/Std/Missing.cure"}},
      {"unsupported async", "E107", {:unsupported_async, "async primitive is unavailable", [line: 2]}},
      {"splice outside quote", "E108", {:splice_outside_quote, :splice, [line: 2]}},
      {"proof chain syntax", "E109",
       {:proof_chain_syntax,
        %Cure.Diagnostic.ProofChainSyntaxProblem{
          kind: :empty_chain,
          observed: :eof,
          expected: :first_expression
        }}},
      {"proof chain mismatch", "E110",
       {:proof_chain_mismatch,
        %Cure.Diagnostic.ProofChainMismatchProblem{
          kind: :wrong_justification,
          step_index: 0,
          expected: :equivalent,
          actual: :reflexive
        }}},
      {"directed rewrite failure", "E111",
       {:rewrite_failed,
        %Cure.Diagnostic.RewriteProblem{
          kind: :no_occurrence,
          direction: :forward,
          occurrences: []
        }}},
      {"simplification failure", "E112",
       {:simplification_failed,
        %Cure.Diagnostic.SimplificationProblem{
          kind: :residual_goal,
          before_goal: :before,
          after_goal: :after,
          progressed_rules: [],
          trace_ids: []
        }}},
      {"induction failure", "E113",
       {:induction_failed,
        %Cure.Diagnostic.InductionProblem{
          kind: :missing_case,
          missing: [:S],
          known: [:Z, :S]
        }}},
      {"defining equation unavailable", "E114",
       {:defining_equation_unavailable,
        %Cure.Diagnostic.DefiningEquationProblem{
          kind: :unknown_equation,
          owner: "identity",
          member: "Missing",
          candidate_equations: []
        }}},
      {"named argument mismatch", "E115",
       {:named_argument_mismatch, :unknown_label,
        %{label: "nope", written: ["nope"], argument_spans: [], label_spans: [], parameter_spans: []}}},
      {"beam write failure", "E096", {:write_failed, "_build/Demo.beam", :eacces}},
      {"beam load failure", "E098", {:load_failed, :badfile}},
      {"beam compilation failure", "E098", {:compilation_failed, [{:bad_form, :detail}]}},
      {"invalid macro unit", "E092", {:invalid_unit, "ms"}},
      {"unknown macro unit", "E092", {:unknown_unit, "ms"}},
      {"invalid board name", "E092", {:invalid_board_name, 42}},
      {"invalid board pins", "E092", :invalid_board_pins},
      {"invalid board capabilities", "E092", :invalid_board_capabilities},
      {"invalid board buses", "E092", :invalid_board_buses},
      {"invalid board flash", "E092", :invalid_board_flash},
      {"board flash offset", "E092", :flash_offset_out_of_bounds},
      {"invalid Core grade", "E100", {:bad_grade, :not_a_grade}},
      {"unknown Core symbol", "E100", {:unknown_symbol, "not_loaded"}},
      {"ill-formed Core term", "E100", {:ill_formed_term, {:not_core, 1}}},
      {"unregistered bounded family", "E093", :bounded_family_unregistered},
      {"reachable absurd branch", "E093", :absurd_in_reachable_position},
      {"opaque elimination", "E093", :opaque_not_eliminable},
      {"non-data case", "E093", :case_scrutinee_not_data},
      {"non-total definition", "E093", :not_total},
      {"non-function application", "E093", :not_a_function},
      {"non-exhaustive pattern", "E093", :coverage},
      {"branch arity", "E093", :branch_arity},
      {"branch type", "E093", :branch_type},
      {"index arity", "E093", :index_arity},
      {"applied non-function", "E093", :applied_non_function},
      {"rewrite expected type", "E093", :rewrite_requires_expected_type},
      {"rewrite proof", "E093", :rewrite_proof_not_equality},
      {"match non-data", "E093", :match_scrutinee_not_data},
      {"mixed rematch arms", "E093", :with_mixed_rematch_arms},
      {"with non-data", "E093", :with_scrutinee_not_data},
      {"too few arguments", "E093", :too_few_arguments},
      {"too many arguments", "E093", :too_many_arguments},
      {"non-variable scrutinee", "E093", :nonvariable_scrutinee},
      {"literal macro capture", "E094", {:expected_literal_capture, %{shape: "Int", line: 1, column: 2}}},
      {"unknown syntax family field", "E092",
       {:unknown_syntax_family_field, %{family: :Expr, field: :field, valid_fields: [:value], line: 1, column: 2}}},
      {"missing syntax family field", "E092",
       {:missing_syntax_family_field, %{family: :Expr, field: :field, line: 1, column: 2}}},
      {"unknown macro obligation capture", "E092",
       {:unknown_macro_obligation_capture,
        %{capture: :capture, interface: :Comparable, available_captures: [:value], line: 1, column: 2}}},
      {"graded let requires variable", "E093", {:graded_let_requires_variable, %{grade: :linear}}},
      {"unknown grade", "E093", {:unknown_grade, %{grade: :future, supported: [:erased, :linear, :affine]}}},
      {"grade requires type", "E093", {:grade_requires_type, %{name: :value, grade: :linear}}},
      {"reserved unit type", "E092", {:unit_type_reserved, %{name: "ms", line: 1, column: 1}}},
      {"duplicate index", "E105", {:duplicate_index, :n}},
      {"multi-with proof", "E093", {:with_multi_proof_unsupported, "proof", []}},
      {"multi-with rematch", "E093", {:with_multi_rematch_unsupported, "rematch", []}},
      {"multi-with arity", "E093", {:with_multi_arity_mismatch, "arity", []}},
      {"multi-with no arms", "E093", {:with_multi_no_arms, "arms", []}},
      {"multi-with inconsistent pattern", "E093", {:with_multi_inconsistent_pattern, "patterns", []}},
      {"duplicate syntax family field", "E092", {:duplicate_syntax_family_field, %{field: :field, line: 1, column: 2}}},
      {"non-associative operator", "E094", {:non_associative, %{operator: :==, next_operator: :==}}},
      {"ambiguous precedence", "E094",
       {:ambiguous_precedence, %{left_group: :left, right_group: :right, operator: :"<?>"}}}
    ]

    compiler_codes = Enum.map(compiler_cases ++ boundary_cases, &elem(&1, 1))
    compiler_fixture_ids = Enum.flat_map(compiler_cases, &compiler_case_fixture_ids/1)

    Enum.with_index(compiler_cases, 1)
    |> Enum.each(fn {compiler_case, audit_index} ->
      {label, expected_code, source, fixture_id} = compiler_case_parts(compiler_case)

      case Cure.Compiler.compile_string(source, emit_events: false) do
        {:ok, module, warnings} ->
          flunk("#{label} unexpectedly compiled as #{inspect(module)} with #{length(warnings)} warning(s)")

        {:error, reason} ->
          {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "#{label}.cure", source)
          assert diagnostic.code == expected_code

          if fixture_id do
            assert {^expected_code, _producer} =
                     Map.fetch!(Cure.Diagnostic.Registry.producer_fixture_inventory(), fixture_id)
          end

          assert diagnostic.primary, "#{label} did not retain an authored source span"
          plain = Renderer.plain(diagnostic, registry)
          assert plain =~ " | ", "#{label} did not render an authored source excerpt"
          assert_no_raw_diagnostic_leaks(plain, label)

          assert Cure.Compiler.Errors.format_with_source(reason, "#{label}.cure", source) =~ expected_code,
                 "#{label} still uses the legacy formatter path"

          terminal =
            Renderer.terminal(
              diagnostic,
              registry,
              Keyword.merge(render_options(), output_device: :standard_error)
            )

          assert Enum.any?(String.split(source, "\n"), &(&1 != "" and String.contains?(terminal, &1)))

          if audit?() do
            print_audit_case(audit_index, label, expected_code, fixture_id, diagnostic, registry)
          else
            IO.puts(:stderr, "[#{label}]\n" <> terminal)
          end
      end
    end)

    compiler_fixture_ids =
      [
        exercise_ambiguous_name_fixture(),
        exercise_kernel_type_mismatch_fixture(),
        exercise_computed_macro_internal_fixture()
        | compiler_fixture_ids
      ]

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures(compiler_fixture_ids,
               only_producers: [:parser]
             )

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures(compiler_fixture_ids,
               only_producers: [:lexer]
             )

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures(compiler_fixture_ids,
               only_producers: [:name_resolution]
             )

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures(compiler_fixture_ids,
               only_producers: [:totality_checker]
             )

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures(compiler_fixture_ids,
               only_producers: [:kernel]
             )

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures(compiler_fixture_ids,
               only_producers: [:macro_expansion]
             )

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures(compiler_fixture_ids,
               only_producers: [:elaboration]
             )

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures(compiler_fixture_ids,
               only_producers: [:pattern_checker, :proof_checker]
             )

    Enum.with_index(boundary_cases, length(compiler_cases) + 1)
    |> Enum.each(fn {{label, expected_code, reason}, audit_index} ->
      {diagnostic, registry} =
        Cure.Compiler.Errors.to_diagnostic(reason, "#{label}.cure", "fn run() -> Int = 1\n")

      assert diagnostic.code == expected_code
      assert_no_raw_diagnostic_leaks(Renderer.plain(diagnostic), label)

      assert Cure.Compiler.Errors.format_with_source(reason, "#{label}.cure", "fn run() -> Int = 1\n") =~
               expected_code,
             "#{label} still uses the legacy source formatter path"

      if audit?(),
        do: print_audit_case(audit_index, label, expected_code, nil, diagnostic, registry)
    end)

    diagnostics = [
      {:file_read, Operational.file_read("demo.cure", :enoent)},
      {:file_write, Operational.file_write("demo.cure", :eacces)},
      {:dependency, Operational.dependency(:locked)},
      {:command, Operational.command_failure("compile", :failed)},
      {:migration_warning,
       Operational.migration_warning(%{rule: :legacy, file: "demo.cure", line: 2, message: "migrate this"})},
      {:compiler_warning, Operational.compiler_warning(%{file: "demo.cure", line: 3, message: "check this"})},
      {:export_unmappable, Operational.export_unmappable("dependent type")},
      {:snap_missing, Operational.snap_missing("gone.cure")},
      {:proof_file_missing, Operational.proof_file_missing("demo.cureproof")},
      {:proof_verification_failed, Operational.proof_verification_failed("Demo#lemma")},
      {:proof_schema_incompatible, Operational.proof_schema_incompatible("version 2")},
      {:snap_schema_incompatible, Operational.snap_schema_incompatible("version 9")},
      {:registry_signature_invalid, Operational.registry_signature_invalid("Demo@1.0.0")},
      {:transparency_log_unreachable, Operational.transparency_log_unreachable(:econnrefused)},
      {:registry_fetch_failed, Operational.registry_fetch_failed(:timeout)},
      {:registry_hash_mismatch, Operational.registry_hash_mismatch("Demo@1.0.0")},
      {:registry_package_not_found, Operational.registry_package_not_found("Demo@1.0.0")},
      {:package_version_conflict, Operational.package_version_conflict("Demo", [">= 1.0", "< 0.9"])},
      {:undocumented_public_function, Operational.undocumented_public_function("demo.cure", 3)},
      {:configuration_warning, Operational.configuration_warning("invalid setting")},
      {:destructive_format_warning, Operational.destructive_format_warning(%{files: ["demo.cure"]})},
      {:usage, Operational.usage("Usage: cure compile FILE")},
      {:artifact, Operational.artifact_error("artifact is invalid")},
      {:internal_failure_operational, Operational.internal_exception(%ArgumentError{message: "boom"}, [])}
    ]

    fixture_inventory = Cure.Diagnostic.Registry.producer_fixture_inventory()

    operational_offset = length(compiler_cases) + length(boundary_cases) + 1

    Enum.with_index(diagnostics, operational_offset)
    |> Enum.each(fn {{fixture_id, diagnostic}, audit_index} ->
      assert {expected_code, _producer} = Map.fetch!(fixture_inventory, fixture_id)
      assert diagnostic.code == expected_code

      if audit?() do
        print_audit_case(audit_index, Atom.to_string(fixture_id), expected_code, fixture_id, diagnostic, nil)
      else
        IO.puts(
          :stderr,
          Renderer.terminal(
            diagnostic,
            nil,
            Keyword.merge(render_options(), output_device: :standard_error)
          )
        )
      end
    end)

    operational_codes = Enum.map(diagnostics, fn {_fixture_id, diagnostic} -> diagnostic.code end)
    exercised_fixture_ids = Enum.map(diagnostics, &elem(&1, 0))

    assert :ok =
             Cure.Diagnostic.Registry.validate_exercised_producer_fixtures(exercised_fixture_ids,
               only_producers: [:operational]
             )

    assert operational_codes ==
             ~w[E095 E096 E097 E098 W001 W000 E068 E070 E065 E066 E067 E069 E041 E042 E038 E039 E040 E030 E008 W002 W003 E099 E100 E101]

    registered_codes = Cure.Diagnostic.Registry.reachable() |> Enum.map(& &1.code) |> MapSet.new()
    covered_codes = MapSet.new(compiler_codes ++ operational_codes)
    missing_codes = MapSet.difference(registered_codes, covered_codes) |> Enum.sort()

    IO.puts(
      :stderr,
      "\nDIAGNOSTIC PATH COVERAGE: #{MapSet.size(covered_codes)}/#{MapSet.size(registered_codes)} registered codes"
    )

    IO.puts(:stderr, "UNCOVERED REGISTERED CODES: " <> Enum.join(missing_codes, ", "))
    assert MapSet.subset?(covered_codes, registered_codes)

    config = Application.get_env(:cure, :diagnostics_exerciser, [])

    if Keyword.get(config, :coverage, false) or audit?() do
      assert missing_codes == [], "diagnostic coverage is incomplete"
    end

    if audit?() do
      IO.puts(
        :stderr,
        "DIAGNOSTIC AUDIT COMPLETE: #{length(compiler_cases) + length(boundary_cases) + length(diagnostics)} cases; " <>
          "#{MapSet.size(registered_codes)} registered codes covered"
      )
    end
  end

  defp assert_no_raw_diagnostic_leaks(plain, label) do
    assert is_binary(plain), "#{label} did not produce plain diagnostic text"
    refute plain =~ "{:"
    refute plain =~ "%{"
    refute plain =~ "Cure.Core."
    refute plain =~ "** ("
    refute plain =~ "lib/cure/"
    refute plain =~ "#Function<"
  end

  defp audit? do
    Keyword.get(Application.get_env(:cure, :diagnostics_exerciser, []), :audit, false)
  end

  defp print_audit_case(index, label, expected_code, fixture_id, diagnostic, registry) do
    entry = Cure.Diagnostic.Registry.fetch!(expected_code)

    fixture =
      case fixture_id do
        nil -> "-"
        fixture_id -> Atom.to_string(fixture_id)
      end

    IO.puts(
      :stderr,
      "\n=== DIAGNOSTIC AUDIT #{index} ===\n" <>
        "label=#{label} code=#{diagnostic.code} key=#{diagnostic.key} " <>
        "subsystem=#{entry.subsystem} fixture=#{fixture} " <>
        "producers=#{Enum.join(Enum.map(entry.producers, &Atom.to_string/1), ",")}\n" <>
        "payload_keys=#{diagnostic.payload |> Map.keys() |> Enum.map(&to_string/1) |> Enum.sort() |> Enum.join(",")}\n" <>
        Renderer.terminal(
          diagnostic,
          registry,
          Keyword.merge(render_options(), output_device: :standard_error)
        )
    )
  end

  defp compiler_case_parts({label, code, source}), do: {label, code, source, nil}
  defp compiler_case_parts({label, code, source, fixture_id}), do: {label, code, source, fixture_id}

  defp compiler_case_fixture_ids({_label, _code, _source}), do: []
  defp compiler_case_fixture_ids({_label, _code, _source, fixture_id}), do: [fixture_id]

  defp exercise_ambiguous_name_fixture do
    tmp = Path.join(System.tmp_dir!(), "cure_diagnostic_ambiguity_#{System.unique_integer([:positive])}")
    File.mkdir_p!(tmp)

    File.write!(Path.join(tmp, "fixture_left.cure"), """
    mod Std.FixtureLeft
      fn shared(value: Int) -> Int = value
    end
    """)

    File.write!(Path.join(tmp, "fixture_right.cure"), """
    mod Std.FixtureRight
      fn shared(value: Int) -> Int = value
    end
    """)

    previous = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, [tmp])

    for fixture <- ["fixture_left.cure", "fixture_right.cure"] do
      path = Path.join(tmp, fixture)

      assert {:ok, module} =
               Cure.Compiler.compile_and_load(File.read!(path),
                 file: path,
                 source_roots: [tmp],
                 emit_events: false
               )

      assert module in [:"Cure.Std.FixtureLeft", :"Cure.Std.FixtureRight"]
    end

    source =
      "mod DiagnosticAmbiguous\n  use Std.FixtureLeft\n  use Std.FixtureRight\n" <>
        "  fn apply(g: (Int) -> Int, value: Int) -> Int = g(value)\n" <>
        "  fn run() -> Int = apply(shared, 1)\nend\n"

    try do
      assert {:error, {:codegen_error, reason}} =
               Cure.Compiler.compile_string(source,
                 file: "ambiguous name.cure",
                 emit_events: false
               )

      {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(reason, "ambiguous name.cure", source)
      assert diagnostic.code == "E089"
      assert diagnostic.primary.span.start_line == 5
      assert diagnostic.primary.span.start_column == 27

      plain = Renderer.plain(diagnostic, registry)
      assert plain =~ "5 |   fn run() -> Int = apply(shared, 1)"
      assert plain =~ "qualification is required here"
      assert plain =~ "Std.FixtureLeft.shared"
      assert_no_raw_diagnostic_leaks(plain, "ambiguous name")

      :ambiguous_name
    after
      if previous,
        do: Process.put(:cure_source_roots, previous),
        else: Process.delete(:cure_source_roots)

      for module <- [:"Cure.Std.FixtureLeft", :"Cure.Std.FixtureRight"] do
        :code.purge(module)
        :code.delete(module)
      end

      File.rm_rf!(tmp)
    end
  end

  defp exercise_kernel_type_mismatch_fixture do
    source = "fn bad() -> Bool = 1\n"
    file = "kernel type mismatch.cure"
    ctx = Cure.Core.Context.empty(Cure.Core.Builtins.seed(Cure.Core.Env.empty()))

    assert {:error, {:conversion_failure, _actual, _expected} = reason} =
             Cure.Core.Kernel.check(ctx, {:int_lit, 1}, {:vdata, :Bool, []})

    span = %Cure.Diagnostic.Span{
      source_id: file,
      path: file,
      start_byte: 19,
      end_byte: 20,
      start_line: 1,
      start_column: 20,
      end_line: 1,
      end_column: 21
    }

    contextual =
      {:source_context, reason,
       %{
         span: span,
         checking: :bad,
         expectation_origin: :annotation,
         expression_category: :literal
       }}

    {diagnostic, registry} = Cure.Compiler.Errors.to_diagnostic(contextual, file, source)
    assert diagnostic.code == "E093"
    assert diagnostic.primary.span == span

    plain = Renderer.plain(diagnostic, registry)
    assert plain =~ "1 | fn bad() -> Bool = 1"
    assert plain =~ "^ this expression has the wrong type"
    assert_no_raw_diagnostic_leaks(plain, "kernel type mismatch")

    :type_mismatch_kernel
  end

  defp exercise_computed_macro_internal_fixture do
    source = "mod M\n  fn result() -> Int = broken\nend\n"
    file = "computed macro internal failure.cure"

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(
        {:computed_macro_error, [keyword: "broken", line: 2, col: 24], {:host_exception, RuntimeError}},
        file,
        source
      )

    assert diagnostic.code == "E101"
    assert diagnostic.primary.span.start_line == 2
    assert Renderer.plain(diagnostic, registry) =~ "this invocation reached the failing compiler path"
    :internal_failure_macro_expansion
  end
end
