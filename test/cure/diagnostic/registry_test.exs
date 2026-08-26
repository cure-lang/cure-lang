defmodule Cure.Diagnostic.RegistryTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.Registry

  test "every catalog code has typed ownership and schema metadata" do
    catalog_codes = Cure.Compiler.Errors.list_all() |> Enum.map(&elem(&1, 0)) |> Enum.sort()
    entries = Registry.entries()

    assert Enum.map(entries, & &1.code) |> Enum.sort() == catalog_codes
    assert Enum.all?(entries, &(&1.status in [:reachable, :retired]))
    assert Enum.all?(entries, &(is_atom(&1.subsystem) and &1.payload_schema == 1))
    assert Enum.all?(entries, &is_atom(&1.key))
    assert Enum.all?(entries, &(is_integer(&1.schema_version) and &1.schema_version >= 1))
    assert Enum.all?(Registry.reachable(), &(is_list(&1.producers) and &1.producers != []))

    assert Enum.all?(Registry.reachable(), fn entry ->
             Map.keys(entry.producer_fixtures) |> Enum.sort() == Enum.sort(entry.producers)
           end)

    assert Enum.all?(Registry.retired(), &(&1.producers == [] and &1.producer_fixtures == %{}))

    assert Enum.all?(entries, fn entry ->
             is_atom(entry.converter) and is_atom(entry.converter_function) and
               Code.ensure_loaded?(entry.converter) and function_exported?(entry.converter, entry.converter_function, 2)
           end)

    assert :ok = Registry.validate(entries)
  end

  test "catalog text is owned by the typed registry, with compatibility delegates" do
    assert Registry.catalog_explanation!("E093") =~ "type"
    assert Registry.Catalog.explanation!("E093") == Registry.catalog_explanation!("E093")
    assert Cure.Compiler.Errors.catalog_explanation!("E093") == Registry.catalog_explanation!("E093")
    assert Cure.Compiler.Errors.catalog_entries() == Registry.catalog_entries()
  end

  test "registry records the operational producer for documentation warnings" do
    assert {:ok, entry} = Registry.fetch("E008")
    assert entry.producers == [:operational]
    assert entry.converter == Cure.Diagnostic.Adapter.Operational
  end

  test "optimistic legacy ownership is retired or narrowed to source-backed producers" do
    e002 = Registry.fetch!("E002")
    assert e002.status == :retired
    assert e002.producers == []
    assert e002.producer_fixtures == %{}
    assert e002.retirement_reason =~ "E091"
    assert {:ok, explanation} = Registry.explain("E002")
    assert explanation =~ "Unbound Variable"

    e003 = Registry.fetch!("E003")
    assert e003.producers == [:elaboration]
    assert e003.producer_fixtures == %{elaboration: :arity_mismatch_elaboration}
    assert File.read!("lib/cure/elab/unify.ex") =~ "{:error, {:arity_mismatch"

    e090 = Registry.fetch!("E090")
    assert e090.producers == [:elaboration]
    assert e090.producer_fixtures == %{elaboration: :unrecognized_pattern_elaboration}
    assert File.read!("lib/cure/elab/elaborator.ex") =~ "{:unsupported_pattern,"
  end

  test "retired codes remain explainable but are excluded from reachable coverage" do
    retired_codes = Enum.map(Registry.retired(), & &1.code)
    assert "E015" in retired_codes
    assert "E002" in retired_codes
    assert "E018" in retired_codes
    assert "E063" in retired_codes
    assert "W088" in retired_codes
    assert length(retired_codes) > 2
    refute Enum.any?(Registry.reachable(), &(&1.code in retired_codes))
    assert {:ok, _} = Cure.Compiler.Errors.explain("E015")
    assert Enum.all?(Registry.retired(), &(is_binary(&1.retirement_reason) and &1.retirement_reason != ""))
    assert Enum.all?(Registry.reachable(), &is_nil(&1.retirement_reason))
    assert Registry.list_all() == Cure.Compiler.Errors.list_all()
    assert Registry.explain("e015") == Cure.Compiler.Errors.explain("E015")

    assert {:ok, e063} = Registry.fetch("E063")
    assert e063.producers == []
    assert e063.producer_fixtures == %{}
    assert e063.retirement_reason =~ "original contextual E094 error"
  end

  test "registry validation rejects duplicate ownership and invalid retirement metadata" do
    entry = Enum.find(Registry.entries(), &(&1.status == :reachable))
    code = entry.code

    assert {:error, {:duplicate_code, ^code}} = Registry.validate([entry, entry])

    sibling = Enum.find(Registry.entries(), &(&1.status == :reachable and &1.code != code))

    assert {:error, {:duplicate_catalog_case, _}} =
             Registry.validate([%{entry | catalog_case: sibling.catalog_case}, sibling])

    assert {:error, {:duplicate_fixture_id, _}} =
             Registry.validate([%{entry | fixture_id: sibling.fixture_id}, sibling])

    assert {:error, {:retired_without_reason, ^code}} =
             Registry.validate([%{entry | status: :retired, producers: [], retirement_reason: nil}])

    assert {:error, {:retired_with_producer, ^code}} =
             Registry.validate([%{entry | status: :retired, retirement_reason: "no longer emitted"}])

    assert {:error, {:reachable_with_retirement_reason, ^code}} =
             Registry.validate([%{entry | retirement_reason: "no longer emitted"}])

    assert {:error, {:missing_producer, ^code}} = Registry.validate([%{entry | producers: []}])

    assert {:error, {:unowned_producer, ^code}} =
             Registry.validate([%{entry | producers: [:unowned_phase]}])

    assert {:error, {:legacy_converter, ^code}} =
             Registry.validate([%{entry | converter: Cure.Compiler.Errors}])

    assert {:error, {:missing_converter_function, ^code}} =
             Registry.validate([%{entry | converter_function: :does_not_exist}])

    assert {:error, {:missing_producer_converter, ^code}} =
             Registry.validate([%{entry | producer_converters: %{}}])

    [producer | _] = entry.producers

    assert {:error, {:missing_producer_converter_function, ^code}} =
             Registry.validate([
               %{entry | producer_converters: Map.put(entry.producer_converters, producer, {String, :does_not_exist})}
             ])

    assert {:error, {:reachable_without_catalog_case, ^code}} =
             Registry.validate([%{entry | catalog_case: nil}])

    assert {:error, {:reachable_without_fixture, ^code}} =
             Registry.validate([%{entry | fixture_id: nil}])
  end

  test "first-party stable diagnostic literals are registered" do
    assert :ok = Registry.validate_sources(Path.wildcard("lib/**/*.ex"))
  end

  test "producer inventory has no legacy owner for reachable codes" do
    assert Enum.all?(Registry.reachable(), fn entry -> :compiler_errors not in entry.producers end)

    assert Map.keys(Registry.producer_inventory()) |> Enum.sort() ==
             Registry.entries() |> Enum.map(& &1.code) |> Enum.sort()

    inventory = Cure.Diagnostic.Registry.Inventory.scan(["lib/cure/diagnostic/registry.ex"])
    assert inventory.error_constructors != []
    assert inventory.formatter_consumers != []
    assert :ok = Registry.validate_reachability()
    assert :ok = Registry.validate_producer_coverage()
    assert :ok = Registry.validate_producer_catalog()
    assert :ok = Cure.Diagnostic.Registry.Inventory.validate(inventory)
  end

  test "E101 records the converter for every trusted producer boundary" do
    entry = Registry.fetch!("E101")

    assert entry.producer_converters == %{
             beam_writer: {Cure.Diagnostic.Adapter.Codegen, :from_error},
             macro_expansion: {Cure.Diagnostic.Adapter, :from_error},
             operational: {Cure.Diagnostic.Adapter.Operational, :from_error}
           }
  end

  test "E091 names its exhaustive family converter for both producer branches" do
    entry = Registry.fetch!("E091")

    assert entry.converter == Cure.Diagnostic.Adapter.Name

    assert entry.producer_converters == %{
             name_resolution: {Cure.Diagnostic.Adapter.Name, :from_error},
             pattern_checker: {Cure.Diagnostic.Adapter.Name, :from_error}
           }
  end

  test "E103 is owned by the exhaustive kernel family converter" do
    entry = Registry.fetch!("E103")
    assert entry.converter == Cure.Diagnostic.Adapter.Kernel
    assert entry.producer_converters == %{kernel: {Cure.Diagnostic.Adapter.Kernel, :from_error}}
  end

  test "kernel conversion failures use the contextual type converter" do
    entry = Registry.fetch!("E093")
    assert entry.producer_converters.kernel == {Cure.Diagnostic.Adapter.Type, :from_error}
    assert entry.producer_converters.elaboration == {Cure.Diagnostic.Adapter, :from_error}
  end

  test "E104 is owned by the exhaustive static-analysis converter" do
    entry = Registry.fetch!("E104")
    assert entry.converter == Cure.Diagnostic.Adapter.StaticAnalysis

    assert entry.producer_converters == %{
             elaboration: {Cure.Diagnostic.Adapter.StaticAnalysis, :from_error}
           }
  end

  test "E117 shares the static-analysis converter without sharing a generic fallback" do
    entry = Registry.fetch!("E117")
    assert entry.converter == Cure.Diagnostic.Adapter.StaticAnalysis

    assert entry.producer_converters == %{
             elaboration: {Cure.Diagnostic.Adapter.StaticAnalysis, :from_error}
           }
  end

  test "totality and pattern coverage have exhaustive static-analysis ownership" do
    for {code, producer} <- [
          {"E013", :totality_checker},
          {"E102", :elaboration},
          {"E118", :elaboration},
          {"E119", :elaboration}
        ] do
      entry = Registry.fetch!(code)
      assert entry.converter == Cure.Diagnostic.Adapter.StaticAnalysis

      assert entry.producer_converters == %{
               producer => {Cure.Diagnostic.Adapter.StaticAnalysis, :from_error}
             }
    end
  end

  test "producer catalog validation requires every code and producer branch independently" do
    entry = Registry.fetch!("E094")
    assert entry.producers |> Enum.sort() == [:lexer, :parser]

    without_lexer = %{entry | producer_fixtures: Map.delete(entry.producer_fixtures, :lexer)}

    assert {:error, {:producer_branches_without_catalog_fixture, [{"E094", :lexer}]}} =
             Registry.validate_producer_catalog([without_lexer])
  end

  test "exercised producer validation rejects missing, duplicate, and invented fixture IDs" do
    operational_ids =
      Registry.producer_fixture_inventory()
      |> Enum.flat_map(fn
        {id, {_code, :operational}} -> [id]
        _ -> []
      end)
      |> Enum.sort()

    assert operational_ids != []

    assert :ok =
             Registry.validate_exercised_producer_fixtures(operational_ids,
               only_producers: [:operational]
             )

    [missing | incomplete] = operational_ids

    assert {:error, {:unexercised_producer_fixtures, [^missing]}} =
             Registry.validate_exercised_producer_fixtures(incomplete,
               only_producers: [:operational]
             )

    assert {:error, {:duplicate_exercised_producer_fixture, [^missing]}} =
             Registry.validate_exercised_producer_fixtures([missing | operational_ids],
               only_producers: [:operational]
             )

    assert {:error, {:unknown_exercised_producer_fixture, [:invented_fixture]}} =
             Registry.validate_exercised_producer_fixtures([:invented_fixture | operational_ids],
               only_producers: [:operational]
             )
  end

  test "inventory rejects new production calls to the legacy compiler formatter" do
    inventory = %{
      error_constructors: [],
      deliberate_raises: [],
      formatter_consumers: [
        %{path: "lib/cure/cli.ex", line: 1, text: "Cure.Compiler.Errors.format_error(reason)"}
      ],
      stderr_sites: []
    }

    assert {:error, {:legacy_formatter_path, [_]}} =
             Cure.Diagnostic.Registry.Inventory.validate(inventory)
  end

  test "inventory rejects new production calls to the legacy source formatter" do
    inventory = %{
      error_constructors: [],
      deliberate_raises: [],
      formatter_consumers: [
        %{
          path: "site/lib/cure_site_web/live/playground_live.ex",
          line: 1,
          text: "Cure.Compiler.Errors.format_with_source(reason, file, source)"
        }
      ],
      stderr_sites: []
    }

    assert {:error, {:legacy_formatter_path, [_]}} =
             Cure.Diagnostic.Registry.Inventory.validate(inventory)
  end

  test "source validation reports an unregistered stable code" do
    path = Path.join(System.tmp_dir!(), "cure-diagnostic-registry-fixture.ex")
    File.write!(path, ~S(defmodule Fixture do
  @code "E999"
end
))

    on_exit(fn -> File.rm(path) end)

    assert {:error, {:unregistered_source_codes, ["E999"]}} = Registry.validate_sources([path])
  end

  test "E101 is reserved for internal compiler exceptions" do
    entry = Registry.fetch!("e101")
    assert entry.key == :internal_compiler_error
    assert entry.severity == :error
    assert entry.status == :reachable

    try do
      raise ArgumentError, "boom"
    rescue
      exception ->
        span =
          Cure.Diagnostic.Span.new(
            source_id: "internal.cure",
            path: "internal.cure",
            start_byte: 0,
            end_byte: 3,
            start_line: 1,
            start_column: 1,
            end_line: 1,
            end_column: 4
          )

        provenance = [
          %Cure.Diagnostic.ProvenanceFrame{
            kind: :generated_declaration,
            name: :derive,
            generated: span
          }
        ]

        diagnostic =
          Cure.Diagnostic.Operational.internal_exception(exception, __STACKTRACE__,
            declaration: :"M#run",
            span: span,
            core_term: {:global, :"M#run"},
            core_trace: [{:global, :"M#run"}],
            expected_type: {:global, :Nat},
            inferred_type: {:global, :String},
            unresolved_global: :"M#missing",
            closure_path: [:"M#run", :"M#missing"],
            provenance: provenance
          )

        assert diagnostic.code == "E101"
        assert diagnostic.payload.fingerprint =~ ~r/^[0-9a-f]{12}$/
        assert diagnostic.primary.span == span
        assert diagnostic.provenance == provenance
        assert diagnostic.payload.declaration == :"M#run"
        assert diagnostic.payload.core_term =~ "M#run"
        assert diagnostic.payload.core_trace == [{:global, :"M#run"}]
        assert diagnostic.payload.expected_type == "{:global, :Nat}"
        assert diagnostic.payload.inferred_type == "{:global, :String}"
        assert diagnostic.payload.unresolved_global == :"M#missing"
        assert diagnostic.payload.closure_path == [:"M#run", :"M#missing"]
        refute Map.has_key?(diagnostic.payload, :stacktrace)
    end

    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      Cure.Diagnostic.Adapter.from_error({:ordinary_unhandled_error, :detail})
    end
  end
end
