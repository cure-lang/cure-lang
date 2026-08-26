defmodule Cure.Diagnostic.Adapter.MacroTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Adapter
  alias Cure.Diagnostic.Adapter.Macro, as: MacroAdapter
  alias Cure.Diagnostic.Renderer
  alias Cure.Diagnostic.SourceRegistry

  test "syntax-family fields and captures retain authored repairs" do
    source = "stte payload other\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:macro, source, "macro.cure")

    {:ok, field} = SourceRegistry.span(registry, :macro, 0, 4)
    {:ok, capture} = SourceRegistry.span(registry, :macro, 5, 12)
    {:ok, first} = SourceRegistry.span(registry, :macro, 13, 18)

    errors = [
      {:unknown_syntax_family_field,
       %{
         family: "Definition",
         field: "stte",
         valid_fields: ["state", "events"],
         span: field
       }},
      {:missing_syntax_family_field, %{family: "Definition", field: "state", span: field}},
      {:unknown_macro_obligation_capture,
       %{
         interface: "Show",
         capture: "payload",
         available_captures: ["paylod", "state"],
         span: capture
       }},
      {:unit_type_reserved, %{name: "Duration", span: field, unit_span: first}},
      {:duplicate_syntax_family_field, %{field: "state", span: field, first_span: first}}
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.primary
      assert direct.suggestions != []
    end

    typo = MacroAdapter.from_error(hd(errors))

    assert [
             %{
               applicability: :machine_applicable,
               edits: [%{span: ^field, replacement: "state"}]
             }
           ] = typo.suggestions

    rendered = Renderer.plain(typo, registry, width: 80)
    assert rendered =~ "UNKNOWN SYNTAX-FAMILY FIELD [E092]"
    assert rendered =~ "^^^^ this field is not declared by the family"
    assert rendered =~ "Hint: Replace it with `state`"
  end

  test "unowned errors are rejected by the macro family boundary" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      MacroAdapter.from_error({:unknown_macro_producer, %{}})
    end
  end

  test "packet validation producers are owned by the macro family" do
    errors = [
      {:invalid_packet_name, :Frame},
      {:invalid_packet_endian, :middle},
      {:unknown_packet_scalar, :u128},
      {:missing_packet_endian, :length},
      {:invalid_packet_field, :bad},
      {:forward_packet_length, :payload, :length},
      {:invalid_packet_crc_fields, :checksum, [:payload]},
      :invalid_packet_field_name,
      :duplicate_packet_field
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_packet_validation
      assert direct.suggestions != []
    end
  end

  test "driver validation producers are owned by the macro family" do
    errors = [
      {:invalid_driver_base, -1},
      :invalid_driver_register,
      :duplicate_driver_register,
      :overlapping_driver_register
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_driver_validation
      assert direct.suggestions != []
    end
  end

  test "board validation producers are owned by the macro family" do
    errors = [
      {:invalid_board_name, :Board},
      {:invalid_board_chip, :chip},
      {:unknown_board_pin, 99},
      {:invalid_board_capability, 8},
      {:invalid_board_bus, :i2c},
      {:unknown_bus_pin, :i2c},
      {:missing_bus_capability, :i2c},
      :invalid_board_definition,
      :missing_board_chip,
      :invalid_board_pins,
      :invalid_board_capabilities,
      :invalid_board_buses,
      :invalid_board_flash,
      :flash_offset_out_of_bounds
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_board_validation
      assert direct.suggestions != []
    end
  end

  test "unit validation producers are owned by the macro family" do
    errors = [
      {:duplicate_unit, "ms"},
      {:invalid_unit, "ms"},
      {:unknown_unit, "ms"},
      {:invalid_unit_literal, :bad, "ms"}
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_unit_validation
      assert direct.suggestions != []
    end
  end

  test "check validation producers are owned by the macro family" do
    errors = [
      {:invalid_check_name, :Checks},
      :invalid_check_property,
      :duplicate_check_property
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_check_validation
      assert direct.suggestions != []
    end
  end

  test "protocol validation producers are owned by the macro family" do
    errors = [
      {:invalid_protocol_name, :Proto},
      {:protocol_role_count, 3},
      {:self_protocol_step, :client},
      {:unknown_choice_decider, :observer},
      {:invalid_protocol_branches, :client},
      {:unprojectable_choice, :server},
      {:unknown_protocol_role, :client, :observer}
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_protocol_validation
      assert direct.suggestions != []
    end
  end

  test "parser and raw-input validation producers are owned by the macro family" do
    errors = [
      {:invalid_parse_name, :Grammar},
      {:left_recursive_parse_production, [:expr]},
      :invalid_parse_productions,
      :invalid_parse_production,
      :duplicate_parse_production,
      {:missing_raw_delimiter, "END"},
      {:invalid_raw_delimiter, :bad},
      :invalid_raw_tokens
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.suggestions != []
    end

    assert MacroAdapter.from_error(:invalid_parse_productions).key == :macro_parse_validation
    assert MacroAdapter.from_error(:invalid_raw_tokens).key == :macro_raw_validation
  end

  test "reducer validation producers are owned by the macro family" do
    errors = [
      {:unknown_reducer_constructor, [:A]},
      {:incomplete_reducer, [:B, :C]},
      {:reducer_arity, :A, 1, 2},
      :invalid_reducer_arms,
      :invalid_reducer_arm,
      :duplicate_reducer_constructor
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_reducer_validation
      assert direct.suggestions != []
    end
  end

  test "syntax decoding producers are owned by the macro family" do
    errors = [
      {:invalid_syntax_node, [], []},
      {:invalid_syntax_node, :bad},
      {:invalid_syntax_leaf, :Node},
      {:invalid_syntax_failure, :bad},
      {:unsupported_syntax_core, :core},
      {:invalid_syntax_attrs, :attrs},
      {:invalid_syntax_attr, :attr},
      {:invalid_syntax_list, :list},
      {:invalid_syntax_string, :string},
      {:invalid_syntax_literal, :literal},
      {:invalid_syntax_pair, :pair}
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_syntax_decode
      assert direct.suggestions != []
    end
  end

  test "syntax integrity producers retain their failing path" do
    path = [{:child, 1}, {:attribute, :span, 0}]

    errors = [
      {:raw_syntax_in_expansion, path},
      {:quoted_syntax_in_expansion, []},
      {:malformed_expansion_syntax, path},
      {:malformed_expansion_attribute, path},
      {:malformed_expansion_map, path},
      {:malformed_expansion_literal, path},
      {:malformed_reflected_syntax, path},
      {:malformed_reflected_attribute, path},
      {:malformed_reflected_map, path},
      {:malformed_reflected_literal, path}
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_syntax_integrity
      assert direct.payload.path == path or direct.payload.path == []
      assert direct.suggestions != []
    end

    assert MacroAdapter.syntax_path_phrase(path) == "`attribute span[0].child[1]`"
  end

  test "module validation producers are owned by the macro family" do
    errors = [
      {:closed_category_extension, [:Expression]},
      {:ambiguous_macro_extension, [:left, :right]},
      {:module_rule_not_fully_consumed, :tail},
      {:not_a_module_rule, :bad},
      :invalid_module_rule_set,
      :invalid_module_rule_bindings,
      :invalid_macro_extension_rules,
      :invalid_macro_extension_rule
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_module_validation
      assert direct.suggestions != []
    end
  end

  test "syntax-family validation producers preserve their reason and related spans" do
    errors = [
      :invalid_macro_rules,
      :expander_without_accepts,
      :accepts_without_syntax_family,
      :accepts_without_expander,
      :multiple_accepts_declarations,
      :multiple_expands_declarations,
      {:unknown_syntax_family, :Expression},
      {:syntax_family_cycle, [:Expression, :Pattern, :Expression]},
      {:duplicate_syntax_family, [:Expression, :Expression]},
      {:duplicate_syntax_family_field, [{:Expression, :span}]}
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :invalid_macro_family
      assert direct.suggestions != []
    end

    details = %{
      reason: {:syntax_family_cycle, [:Expression, :Pattern, :Expression]},
      related_spans: []
    }

    direct = MacroAdapter.from_error({:invalid_macro_family, details})
    assert Adapter.from_error({:invalid_macro_family, details}) == direct
    assert direct.payload == details
  end

  test "macro schema and fuzz producers are owned by the macro family" do
    errors = [
      {:invalid_macro_diagnostics, :bad},
      {:invalid_macro_diagnostic, :bad},
      {:invalid_macro_segment, :segment},
      {:unsupported_surface_filler, :value},
      {:missing_hole_filler, :name},
      {:invalid_repeated_hole_filler, :name},
      :not_a_nat,
      :invalid_macro_fuzz_rule,
      :invalid_macro_fuzz_bindings
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key in [:macro_diagnostic_schema, :macro_fuzz_input]
      assert direct.suggestions != []
    end

    assert MacroAdapter.from_error({:missing_hole_filler, :payload}).payload == %{
             kind: :missing_hole_filler,
             hole: "payload"
           }
  end

  test "macro declaration validation retains contextual details" do
    errors = [
      {:missing_diagnosis, [{:failure, :bad}]},
      {:rule_unpinned, [:run]},
      {:example_mismatch, [%{keyword: :run}]},
      {:example_type_mismatch, [%{keyword: :run}]},
      {:computed_example_error, [%{keyword: :run}]},
      {:source_context, {:reserved_syntax_field, :context, [:run]}, %{hole_spans: []}},
      {:source_context, {:unsupported_hole_type, :Proof}, %{hole_spans: []}}
    ]

    for error <- errors do
      direct = MacroAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E092"
      assert direct.key == :macro_validation_failed
      assert direct.suggestions != []
    end
  end

  test "expansion failures blame authored invocation frames" do
    source = "outer inner\n"

    registry =
      SourceRegistry.new()
      |> SourceRegistry.register(:expansion, source, "expansion.cure")

    {:ok, outer} = SourceRegistry.span(registry, :expansion, 0, 5)
    {:ok, inner} = SourceRegistry.span(registry, :expansion, 6, 11)

    frames = [
      %{keyword: "outer", invocation: outer},
      %{keyword: "inner", invocation: inner, parent: outer}
    ]

    errors = [
      {:macro_expansion_cycle, frames},
      {:macro_expansion_budget, :expansion_count, frames},
      {:expansion_ill_typed, %{keyword: "inner", input: :input, expansion: :output, reason: :bad}}
    ]

    for error <- errors do
      opts = [span: inner]
      direct = MacroAdapter.from_error(error, opts)
      assert Adapter.from_error(error, opts) == direct
      assert direct.code == "E092"
      assert direct.primary.span == inner
    end

    cycle = MacroAdapter.from_error(hd(errors))
    assert hd(cycle.secondary).span == outer
    assert Enum.map(cycle.provenance, & &1.name) == ["outer", "inner"]
    assert cycle.suggestions != []

    rendered = Renderer.plain(cycle, registry, width: 80)
    assert rendered =~ "MACRO EXPANSION CYCLE [E092]"
    assert rendered =~ "this invocation closes the expansion cycle"
    assert rendered =~ "Hint: Make recursive macro expansion consume input"
  end
end
