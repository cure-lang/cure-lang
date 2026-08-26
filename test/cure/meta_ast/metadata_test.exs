defmodule Cure.MetaAST.MetadataTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{ProvenanceFrame, Span}
  alias Cure.MetaAST.{Metadata, SourceInfo}

  defp span(start_byte, end_byte) do
    %Span{
      source_id: :sentinel,
      path: "sentinel.cure",
      start_byte: start_byte,
      end_byte: end_byte,
      start_line: 1,
      start_column: start_byte + 1,
      end_line: 1,
      end_column: end_byte + 1
    }
  end

  test "canonical source information replaces legacy keys" do
    whole = span(0, 4)
    name = span(0, 2)
    info = %SourceInfo{whole: whole, name: name}

    metadata = Metadata.put_source_info([line: 1, span: whole, name_span: name, semantic: :kept], info)
    assert Keyword.get(metadata, :semantic) == :kept
    assert Keyword.get(metadata, :source_info) == info
    refute Keyword.has_key?(metadata, :span)

    assert Metadata.source_info(span: whole, name_span: name).whole == whole
    assert Metadata.source_info(span: whole, name_span: name).name == name
  end

  test "source lookup tolerates generated mixed metadata without source fields" do
    generated_child = {:param, [type: {:variable, [], "Type"}], "value"}

    assert Metadata.source_info([generated_child, semantic: :kept]) == nil
  end

  test "recursive projection strips metadata stored inside metadata values" do
    source = span(0, 1)

    decorated =
      {:function_def,
       [
         params: [{:param, [type: {:variable, [span: source], "Int"}, span: source], "x"}],
         source_info: %SourceInfo{whole: source}
       ], [{:variable, [span: source], "x"}]}

    plain =
      {:function_def,
       [
         params: [{:param, [type: {:variable, [], "Int"}], "x"}]
       ], [{:variable, [], "x"}]}

    assert Metadata.semantic_equal?(decorated, plain)
    assert Metadata.semantic_key(decorated) == plain
  end

  test "canonical source information preserves every specified role" do
    spans = for index <- 0..17, do: span(index, index + 1)

    info = %SourceInfo{
      whole: Enum.at(spans, 0),
      name: Enum.at(spans, 1),
      callee: Enum.at(spans, 2),
      operator: Enum.at(spans, 3),
      operands: Enum.slice(spans, 4, 2),
      arguments: Enum.slice(spans, 6, 2),
      argument_labels: [Enum.at(spans, 6), nil],
      annotation: Enum.at(spans, 8),
      body: Enum.at(spans, 9),
      condition: Enum.at(spans, 10),
      then_branch: Enum.at(spans, 11),
      else_branch: Enum.at(spans, 12),
      pattern: Enum.at(spans, 13),
      guard: Enum.at(spans, 14),
      branches: [Enum.at(spans, 15)],
      fields: %{field: Enum.at(spans, 16)},
      opener: Enum.at(spans, 17),
      closer: Enum.at(spans, 17),
      provenance: [%ProvenanceFrame{kind: :source, name: "sentinel", invocation: Enum.at(spans, 0)}]
    }

    meta = Metadata.put_source_info([semantic: :kept], info)
    assert Metadata.source_info(meta) == info
    assert Metadata.drop_source_info(meta) == [semantic: :kept]
  end

  test "recursive projection reaches every kind of metadata-held subterm" do
    source = span(0, 1)
    located = fn tag -> {tag, [source_info: %SourceInfo{whole: source}], []} end

    decorated =
      {:function_def,
       [
         params: [located.(:parameter_type)],
         return_type: located.(:return_type),
         guards: [located.(:guard)],
         constraints: %{constraint: located.(:constraint)},
         pattern: located.(:pattern),
         clauses: [{:clause_key, located.(:clause)}],
         semantic: :kept
       ], [located.(:body)]}

    expected =
      {:function_def,
       [
         params: [{:parameter_type, [], []}],
         return_type: {:return_type, [], []},
         guards: [{:guard, [], []}],
         constraints: %{constraint: {:constraint, [], []}},
         pattern: {:pattern, [], []},
         clauses: [{:clause_key, {:clause, [], []}}],
         semantic: :kept
       ], [{:body, [], []}]}

    assert Metadata.semantic_key(decorated) == expected
  end

  test "projection leaves ordinary structs and opaque payloads atomic" do
    range = 1..3
    payload = {:node, [source_info: %SourceInfo{whole: span(0, 1)}, semantic: range], [range]}

    assert {:node, [semantic: ^range], [^range]} = Metadata.semantic_key(payload)
  end
end
