defmodule Cure.Diagnostic.Adapter.NameTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, Renderer, SourceRegistry}
  alias Cure.Diagnostic.Adapter.Name, as: NameAdapter

  test "the name family retains candidate identity and emits a unique typo edit" do
    source = "pritn\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:name_test, source, "name.cure")
    {:ok, span} = SourceRegistry.span(registry, :name_test, 0, 5)

    candidate = %{
      id: {:value, :"Std.Io", :print, 1},
      name: "print",
      namespace: :value,
      visibility: :public,
      arity: 1,
      owner: :"Std.Io",
      imported: true,
      requires_import: false,
      origin: :import
    }

    opts = [span: span, candidates: [candidate], arity: 1]
    direct = NameAdapter.unknown_name(:value, "pritn", opts)

    assert Adapter.unknown_name(:value, "pritn", opts) == direct
    assert [detail] = direct.payload.candidate_details
    assert detail.candidate_id == candidate.id
    assert detail.owner == :"Std.Io"
    assert detail.namespace == :value
    assert detail.origin == :import

    assert [suggestion] = direct.suggestions
    assert suggestion.applicability == :machine_applicable
    assert [%{span: ^span, replacement: "print"}] = suggestion.edits

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- UNKNOWN VALUE [E091] ---------------------------------------------- name.cure

             `pritn` is not available in this value namespace.

             at name.cure:1:1
             1 | pritn
               | ^^^^^ `pritn` was not found

             Hint: Did you mean `print`?
             """
             |> String.trim_trailing()
  end

  test "an unavailable candidate remains qualified and never becomes a speculative edit" do
    diagnostic =
      NameAdapter.unknown_name(:value, "pritn",
        candidates: [
          %{
            id: :qualified_print,
            name: "print",
            namespace: :value,
            owner: :"Std.Io",
            visibility: :public,
            imported: false,
            requires_import: true,
            origin: :stdlib
          }
        ]
      )

    assert diagnostic.payload.candidate_details |> hd() |> Map.take([:candidate_id, :owner, :requires_import]) ==
             %{candidate_id: :qualified_print, owner: :"Std.Io", requires_import: true}

    assert [suggestion] = diagnostic.suggestions
    assert suggestion.applicability == :maybe_incorrect
    assert suggestion.edits == []
    assert suggestion.message =~ "`Std.Io.print`"
    assert suggestion.message =~ "Qualify it or import its module"
  end

  test "raw producer variants route exhaustively through the name family" do
    variants = [
      {:unknown_global, :missing},
      {:unbound_var, :missing},
      {:unknown_family, :Missing},
      {:unknown_ctor, :Missing},
      {:unknown_constructor, :Missing},
      {:unknown_field, :Point, :z, [:x, :y]},
      {:no_such_interface, :Missing},
      {:unknown_interface_method, :Eq, :missing}
    ]

    for error <- variants do
      assert NameAdapter.from_error(error) == Adapter.from_error(error)
      assert NameAdapter.from_error(error).code == "E091"
    end

    diagnostic = NameAdapter.from_error({:ambiguous_name, :shared, ["Left", "Right"]})
    assert diagnostic == Adapter.from_error({:ambiguous_name, :shared, ["Left", "Right"]})
    assert diagnostic.code == "E089"
    assert diagnostic.payload == %{namespace: :value, name: "shared", owners: ["Left", "Right"]}
    assert hd(diagnostic.suggestions).message =~ "`Left.shared` or `Right.shared`"

    method = NameAdapter.from_error({:ambiguous_method, :size, [:Eqs, :Ord]})
    assert method == Adapter.from_error({:ambiguous_method, :size, [:Eqs, :Ord]})
    assert method.code == "E089"
    assert method.payload.kind == :ambiguous_method

    duplicate = NameAdapter.from_error({:duplicate_module_identity, "Demo", "a.cure", "b.cure"})
    assert duplicate == Adapter.from_error({:duplicate_module_identity, "Demo", "a.cure", "b.cure"})
    assert duplicate.code == "E087"
    assert duplicate.payload.paths == ["a.cure", "b.cure"]

    operator = NameAdapter.from_error({:precedence_cycle, [:Additive, :Multiplicative]})
    assert operator == Adapter.from_error({:precedence_cycle, [:Additive, :Multiplicative]})
    assert operator.code == "E106"

    sibling = NameAdapter.from_error({:sibling_module_collision, :run, [:Left, :Right]})
    assert sibling == Adapter.from_error({:sibling_module_collision, :run, [:Left, :Right]})
    assert sibling.code == "E105"

    overload = NameAdapter.from_error({:overlapping_overload, :move, 1})
    assert overload == Adapter.from_error({:overlapping_overload, :move, 1})
    assert overload.code == "E105"

    instance = NameAdapter.from_error({:overlapping_instance, :Eqs, :Int})
    assert instance == Adapter.from_error({:overlapping_instance, :Eqs, :Int})
    assert instance.code == "E105"

    named_instance = NameAdapter.from_error({:overlapping_named_instance, :fast, :Eqs, :Int})
    assert named_instance == Adapter.from_error({:overlapping_named_instance, :fast, :Eqs, :Int})
    assert named_instance.code == "E105"

    duplicate = NameAdapter.from_error({:duplicate_parameter, :value})
    assert duplicate == Adapter.from_error({:duplicate_parameter, :value})
    assert duplicate.code == "E105"

    conformance = NameAdapter.from_error({:method_signature_mismatch, :Eqs, :eqs})
    assert conformance == Adapter.from_error({:method_signature_mismatch, :Eqs, :eqs})
    assert conformance.code == "E105"

    head = NameAdapter.from_error({:instance_head_ill_formed, :not_type_head})
    assert head == Adapter.from_error({:instance_head_ill_formed, :not_type_head})
    assert head.code == "E105"

    superinterface = NameAdapter.from_error({:missing_superinterface, :Ord, :Eq, :Int})
    assert superinterface == Adapter.from_error({:missing_superinterface, :Ord, :Eq, :Int})
    assert superinterface.code == "E105"

    deriving = NameAdapter.from_error({:cannot_derive, :Equatable})
    assert deriving == Adapter.from_error({:cannot_derive, :Equatable})
    assert deriving.code == "E105"

    head_kind = NameAdapter.from_error({:inconsistent_head_kind, :Eq})
    assert head_kind == Adapter.from_error({:inconsistent_head_kind, :Eq})
    assert head_kind.code == "E105"

    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      NameAdapter.from_error({:ordinary_type_failure, :not_a_name_error})
    end
  end

  test "shadowing producers retain their source labels through the name family" do
    context = %{span: nil, checking: :run}

    guard_error =
      {:source_context, {:unsupported_guard, %{reason: :shadowed, name: "x", site: :body}}, context}

    union_error =
      {:source_context, {:unsupported_pattern, %{reason: :shadowed_tuple, name: "x"}}, context}

    for error <- [guard_error, union_error] do
      assert NameAdapter.from_error(error) == Adapter.from_error(error)
      assert NameAdapter.from_error(error).code == "E090"
    end
  end

  test "module identity and alias-cycle conflicts are owned by the name family" do
    errors = [
      {:cyclic_typealiases, [:A, :B, :A]},
      {:module_identity_mismatch, "App.Root", "App.Other", "lib/root.cure"},
      {:module_path_identity_mismatch, "lib/root.cure", "App.Other", "App.Root"},
      :shadowed
    ]

    for error <- errors do
      direct = NameAdapter.from_error(error)
      assert Adapter.from_error(error) == direct
      assert direct.code == "E105"
      assert direct.key == :declaration_conflict
    end
  end
end
