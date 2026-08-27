defmodule Cure.Compiler.MacroSyntax do
  @moduledoc """
  Reflection bridge between the parser AST and the generic `Std.Syntax` value a
  Tier-3 `computed by` elab operates on (macro-facility design §3). TCB delta
  zero — pure frontend reflection; the elab's output is re-elaborated + kernel
  checked (K3 firewall). This slice handles the Elixir mirror repr; slice 3
  maps it to Core values of `Std.Syntax` and runs the elab.
  """

  alias Cure.Diagnostic.{ProvenanceFrame, Span}
  alias Cure.MetaAST.{Metadata, SourceInfo}

  @source_info_attr :cure_source_info
  @source_info_tag :__cure_source_info_v1__
  @span_tag :__cure_span_v1__
  @provenance_tag :__cure_provenance_v1__
  @map_tag :__cure_source_map_v1__
  @list_tag :__cure_source_list_v1__
  @tuple_tag :__cure_source_tuple_v1__

  @doc """
  Lower internal standard-library macro markers into ordinary parser AST.

  The marker keeps a macro template from recursively matching its own public
  keyword. It disappears here; downstream elaboration sees an ordinary call.
  """
  @spec lower_internal(term()) :: {:ok, tuple()} | :not_internal | {:error, term()}
  def lower_internal({:function_call, meta, []}) when is_list(meta) do
    case Keyword.get(meta, :name) do
      "__optic_lens_first" -> {:ok, {:function_call, Keyword.put(meta, :name, "first_lens"), []}}
      "__optic_lens_second" -> {:ok, {:function_call, Keyword.put(meta, :name, "second_lens"), []}}
      _ -> :not_internal
    end
  end

  def lower_internal({:unit_value, meta, []}) when is_list(meta),
    do: {:ok, {:unit_value, meta}}

  def lower_internal(_ast), do: :not_internal

  @doc """
  Lower internal syntax markers throughout a generated AST tree.

  Top-level macro results pass through the parser's marker hook, while lifted
  modules are validated directly by `LiftModule`. Keeping the recursive bridge
  here makes both paths interpret the same safe syntax constructors.
  """
  @spec lower_internal_tree(term()) :: term()
  def lower_internal_tree(ast) when is_list(ast),
    do: Enum.map(ast, &lower_internal_tree/1)

  def lower_internal_tree({tag, meta, children}) when is_list(meta) and is_list(children) do
    lowered = {tag, meta, Enum.map(children, &lower_internal_tree/1)}

    case lower_internal(lowered) do
      {:ok, value} -> value
      :not_internal -> lowered
    end
  end

  def lower_internal_tree(ast), do: ast

  @type synlit ::
          {:s_int, integer}
          | {:s_char, non_neg_integer()}
          | {:s_float, float}
          | {:s_str, String.t()}
          | {:s_bool, boolean}
          | {:s_atom, atom}
          | {:s_list, [synlit]}
          | {:s_syntax, repr}
          | {:s_map, [{synlit, synlit}]}
          | :s_opaque
  @type repr ::
          {:syn_node, atom, [{atom, synlit}], [repr]}
          | {:syn_leaf, atom, [{atom, synlit}], synlit}
          | {:syn_raw, synlit}
          | {:syn_quoted, repr}
          | {:syn_failure, atom, [repr]}
          # Quasiquote splice holes (SP5.1). The second element is the RAW
          # surface AST of the spliced expression, kept un-reflected so
          # `lower_quote/1` re-emits it verbatim for the ordinary elaborator.
          | {:syn_splice, term()}
          | {:syn_splice_group, term()}

  # -- to_syntax: parser AST -> repr -----------------------------------------

  # `to_syntax/1` is called recursively over every element found in a node's
  # children list (via `Enum.map(third, &to_syntax/1)`), but not every such
  # element is a well-formed `{tag, meta, third}` triple: an `impossible`
  # match-arm body is the bare atom `nil` (see parse_match_arm_tail/2) -- which
  # matches neither clause below. Rather than crash on real, reachable parser
  # output, fall back to a raw leaf: scalars (like `nil`) round-trip exactly via
  # `synlit`, and any non-conforming tuple reflects opaquely, same as an
  # irreducible native term (e.g. a compiled regex) -- honest, not a crash.
  @spec to_syntax(term()) :: repr
  def to_syntax({:quoted_syntax, _meta, [inner]}), do: {:syn_quoted, to_syntax(inner)}

  # Quasiquote splice holes (SP5.1). Keep the inner expression RAW (do not
  # reflect it): `lower_quote/1` re-emits it verbatim so the ordinary
  # elaborator types and lowers the spliced `Syntax` / `List(Syntax)` value.
  def to_syntax({:splice, _meta, [inner]}), do: {:syn_splice, inner}
  def to_syntax({:splice_group, _meta, [inner]}), do: {:syn_splice_group, inner}

  def to_syntax({:family_option, meta, []}) when is_list(meta),
    do: {:syn_leaf, :option_none, [], :s_opaque}

  def to_syntax({:family_option, meta, [value]}) when is_list(meta),
    do: {:syn_node, :option_some, [], [to_syntax(value)]}

  # Preserve the parser's generic identifier-shape fact for source-defined
  # syntax analysis. A reflected macro must distinguish a Pascal constructor
  # head from a lowercase variable without a domain-specific compiler rule.
  def to_syntax({:variable, meta, name}) when is_list(meta) and is_binary(name) do
    extra = [
      {:pascal_case, {:s_bool, pascal_case?(name)}},
      {:constructor_key, {:s_atom, String.to_atom(name <> "/0")}},
      {:variable_name, {:s_atom, String.to_atom(name)}}
    ]

    {:syn_leaf, :variable, attrs(meta) ++ extra, synlit(name)}
  end

  def to_syntax({:function_call, meta, args}) when is_list(meta) and is_list(args) do
    name = Keyword.get(meta, :name)

    extra =
      if is_binary(name),
        do: [
          {:pascal_case, {:s_bool, pascal_case?(name)}},
          {:constructor_key, {:s_atom, String.to_atom(name <> "/" <> Integer.to_string(length(args)))}}
        ],
        else: []

    {:syn_node, :function_call, attrs(meta) ++ extra, Enum.map(args, &to_syntax/1)}
  end

  def to_syntax({tag, meta, third}) when is_list(third) do
    {:syn_node, tag, attrs(meta), Enum.map(third, &to_syntax/1)}
  end

  def to_syntax({tag, meta, scalar}) when is_atom(tag) and is_list(meta) do
    {:syn_leaf, tag, attrs(meta), synlit(scalar)}
  end

  def to_syntax(other), do: {:syn_raw, synlit(other)}

  @doc "Convert the host reflection representation to the native constructor representation used by compiled Cure code."
  @spec to_runtime(repr()) :: term()
  def to_runtime({:syn_node, tag, attrs, kids}),
    do: {:Node, tag, runtime_attrs(attrs), Enum.map(kids, &to_runtime/1)}

  def to_runtime({:syn_leaf, tag, attrs, lit}),
    do: {:Leaf, tag, runtime_attrs(attrs), synlit_to_runtime(lit)}

  def to_runtime({:syn_raw, lit}), do: {:Raw, synlit_to_runtime(lit)}
  def to_runtime({:syn_quoted, inner}), do: {:Quoted, to_runtime(inner)}
  def to_runtime({:syn_failure, name, args}), do: {:Failure, name, Enum.map(args, &to_runtime/1)}

  @doc "Encode a structured macro input as the erased arguments of its compiled expander."
  @spec to_runtime_direct_inputs(repr(), [String.t()], map()) :: [term()]
  def to_runtime_direct_inputs({:syn_node, _tag, _attrs, kids}, fields, field_types) do
    fields
    |> Enum.zip(kids)
    |> Enum.map(fn {field, kid} -> runtime_record_field(kid, Map.get(field_types, field), [], field) end)
  end

  def to_runtime_direct_inputs(repr, _fields, _field_types), do: [to_runtime(repr)]

  defp runtime_record_field(kid, {:optional, inner}, repeated, field) do
    case kid do
      {:syn_leaf, :option_none, _attrs, :s_opaque} -> :none
      {:syn_node, :option_some, _attrs, [value]} -> {:some, runtime_record_field(value, inner, repeated, field)}
      value -> {:some, runtime_record_field(value, inner, repeated, field)}
    end
  end

  defp runtime_record_field(kid, {:record, nested_name, nested_fields}, repeated, field) do
    encode = fn item -> runtime_nested_record(item, nested_name, nested_fields) end

    if field in repeated,
      do: kid |> nested_record_items() |> Enum.map(encode),
      else: encode.(kid)
  end

  defp runtime_record_field(kid, {:primitive, shape}, repeated, field) do
    if field in repeated do
      kid
      |> runtime_syntax_items()
      |> Enum.map(&runtime_primitive(&1, shape))
    else
      runtime_primitive(kid, shape)
    end
  end

  defp runtime_record_field(kid, :syntax_list, _repeated, _field),
    do: kid |> runtime_syntax_items() |> Enum.map(&to_runtime/1)

  defp runtime_record_field(kid, _type, repeated, field) do
    if field in repeated,
      do: kid |> runtime_syntax_items() |> Enum.map(&to_runtime/1),
      else: to_runtime(kid)
  end

  defp runtime_nested_record({:syn_node, _tag, _attrs, kids}, name, fields) do
    repeated =
      fields
      |> Enum.filter(&(Map.get(&1, :cardinality) in [:repeated, :one_or_more]))
      |> Enum.map(& &1.name)

    field_types = family_field_types(fields)

    args =
      fields
      |> Enum.zip(kids)
      |> Enum.map(fn {field, kid} ->
        runtime_record_field(kid, Map.get(field_types, field.name), repeated, field.name)
      end)

    List.to_tuple([runtime_constructor_name(name) | args])
  end

  defp runtime_nested_record(repr, _name, _fields), do: to_runtime(repr)

  defp runtime_constructor_name(name) do
    name
    |> Cure.Elab.Name.base()
    |> String.to_atom()
  end

  defp runtime_syntax_items({:syn_raw, {:s_list, [{:s_list, items}]}}),
    do: Enum.map(items, &nested_record_item/1)

  defp runtime_syntax_items({:syn_raw, {:s_list, items}}),
    do: Enum.map(items, &nested_record_item/1)

  defp runtime_syntax_items(item), do: [item]

  defp runtime_primitive({:syn_leaf, :literal, _attrs, {:s_int, value}}, "Int"), do: value
  defp runtime_primitive({:syn_raw, {:s_int, value}}, "Int"), do: value
  defp runtime_primitive({:syn_leaf, :literal, _attrs, {:s_float, value}}, "Float"), do: value
  defp runtime_primitive({:syn_raw, {:s_float, value}}, "Float"), do: value
  defp runtime_primitive({:syn_leaf, :literal, _attrs, {:s_atom, value}}, "Atom"), do: value
  defp runtime_primitive({:syn_raw, {:s_atom, value}}, "Atom"), do: value
  defp runtime_primitive({:syn_leaf, :literal, _attrs, {:s_bool, value}}, "Bool"), do: value
  defp runtime_primitive({:syn_raw, {:s_bool, value}}, "Bool"), do: value
  defp runtime_primitive(repr, _shape), do: to_runtime(repr)

  defp runtime_attrs(attrs), do: Enum.map(attrs, fn {key, value} -> {:KV, key, synlit_to_runtime(value)} end)

  defp synlit_to_runtime({:s_int, value}), do: {:SInt, value}
  defp synlit_to_runtime({:s_char, value}), do: {:SChar, value}
  defp synlit_to_runtime({:s_float, value}), do: {:SFloat, value}
  # `{:String, chars}` and not the bare charlist: `List` erases to a native list but
  # the nominal `String` constructor survives erasure, so this mirrors `to_core_string/1`.
  defp synlit_to_runtime({:s_str, value}) when is_binary(value),
    do: {:SStr, {:String, String.to_charlist(value)}}

  defp synlit_to_runtime({:s_bool, value}), do: {:SBool, value}
  defp synlit_to_runtime({:s_atom, value}), do: {:SAtom, value}
  defp synlit_to_runtime({:s_list, values}), do: {:SList, Enum.map(values, &synlit_to_runtime/1)}
  defp synlit_to_runtime({:s_syntax, value}), do: {:SSyntax, to_runtime(value)}

  defp synlit_to_runtime({:s_map, pairs}),
    do: {:SMap, Enum.map(pairs, fn {key, value} -> {:SPair, synlit_to_runtime(key), synlit_to_runtime(value)} end)}

  defp synlit_to_runtime(:s_opaque), do: :SOpaque

  # -- quote lowering: quoted form -> Std.Syntax builder surface AST ----------

  @doc """
  Lower a `quote <form>` inner AST to an ordinary Cure surface expression that
  builds the corresponding `Std.Syntax` value (SP5.1).

  This is the parse-time expansion of `quote`: reflect the quoted form with
  `to_syntax/1` (so `from_syntax` regenerates it exactly — `from_syntax ∘
  to_syntax = id`), then map each `repr` node to its `Std.Syntax` constructor
  application. A `$(e)` splice hole becomes the spliced expression `e`; a
  `$(e ...)` group splice becomes `e` joined into the enclosing child list with
  `Std.List.append`. The result re-enters the ordinary elaborator, so implicit
  insertion, constructor resolution and list typing are handled there — no Core
  is hand-built (TCB delta 0). The enclosing module must `use Std.Syntax` (and
  `use Std.List` when group splices are present), exactly as a hand-written
  builder expression would.
  """
  @spec lower_quote(term()) :: term()
  def lower_quote(inner), do: repr_to_ast(to_syntax(inner))

  # A splice hole in term position IS the spliced expression.
  defp repr_to_ast({:syn_splice, inner}), do: inner

  # A group splice reaching term position (rather than a child-list position)
  # has no enclosing sequence to flatten into — a category error surfaced by
  # the elaborator's orphan-splice check. Emit it as a bare `Std.List` value so
  # the type mismatch (`List(Syntax)` where `Syntax` is expected) is reported.
  defp repr_to_ast({:syn_splice_group, inner}), do: inner

  defp repr_to_ast({:syn_node, tag, attrs, kids}),
    do: qq_call("Node", [qq_atom(tag), attrs_ast(attrs), kids_ast(kids)])

  defp repr_to_ast({:syn_leaf, tag, attrs, lit}),
    do: qq_call("Leaf", [qq_atom(tag), attrs_ast(attrs), synlit_ast(lit)])

  defp repr_to_ast({:syn_raw, lit}), do: qq_call("Raw", [synlit_ast(lit)])
  defp repr_to_ast({:syn_quoted, inner}), do: qq_call("Quoted", [repr_to_ast(inner)])

  defp repr_to_ast({:syn_failure, name, args}),
    do: qq_call("Failure", [qq_atom(name), qq_list(Enum.map(args, &repr_to_ast/1))])

  # Attribute list: `List(Attr)` where `Attr = KV(Atom, SynLit)`.
  defp attrs_ast(attrs),
    do: qq_list(Enum.map(attrs, fn {key, lit} -> qq_call("KV", [qq_atom(key), synlit_ast(lit)]) end))

  # Child list, splicing groups. Runs of ordinary children become list
  # literals; each `$(e ...)` group contributes its `List(Syntax)` value; the
  # segments are joined left-to-right with `Std.List.append`. With no group
  # splice this is a single list literal (clean Core — identical to a
  # hand-written `[a, b, c]`).
  defp kids_ast(kids), do: kids |> chunk_kids() |> segments_to_ast()

  defp chunk_kids([]), do: []
  defp chunk_kids([{:syn_splice_group, inner} | rest]), do: [{:group, inner} | chunk_kids(rest)]

  defp chunk_kids([kid | rest]) do
    {statics, tail} = Enum.split_while(rest, &(not match?({:syn_splice_group, _}, &1)))
    [{:static, Enum.map([kid | statics], &repr_to_ast/1)} | chunk_kids(tail)]
  end

  defp segments_to_ast([]), do: qq_list([])
  defp segments_to_ast([{:static, asts}]), do: qq_list(asts)
  defp segments_to_ast([{:group, inner}]), do: inner
  defp segments_to_ast([{:static, asts} | rest]), do: qq_append(qq_list(asts), segments_to_ast(rest))
  defp segments_to_ast([{:group, inner} | rest]), do: qq_append(inner, segments_to_ast(rest))

  defp synlit_ast({:s_int, n}), do: qq_call("SInt", [qq_lit(:integer, n)])
  defp synlit_ast({:s_char, n}), do: qq_call("SChar", [qq_lit(:char, n)])
  defp synlit_ast({:s_float, f}), do: qq_call("SFloat", [qq_lit(:float, f)])
  defp synlit_ast({:s_str, s}), do: qq_call("SStr", [qq_lit(:string, s)])
  defp synlit_ast({:s_bool, b}), do: qq_call("SBool", [qq_lit(:boolean, b)])
  defp synlit_ast({:s_atom, a}), do: qq_call("SAtom", [qq_atom(a)])
  defp synlit_ast({:s_list, items}), do: qq_call("SList", [qq_list(Enum.map(items, &synlit_ast/1))])
  defp synlit_ast({:s_syntax, inner}), do: qq_call("SSyntax", [repr_to_ast(inner)])

  defp synlit_ast({:s_map, pairs}),
    do:
      qq_call("SMap", [
        qq_list(Enum.map(pairs, fn {k, v} -> qq_call("SPair", [synlit_ast(k), synlit_ast(v)]) end))
      ])

  defp synlit_ast(:s_opaque), do: qq_call("SOpaque", [])

  # Surface-AST builders. The `line`/`col` are cosmetic here — this AST is
  # generated, not sourced — so a fixed origin keeps the shape stable.
  defp qq_call(name, args), do: {:function_call, [name: name, line: 0, col: 0], args}
  defp qq_append(a, b), do: qq_call("append", [a, b])
  defp qq_list(items), do: {:list, [line: 0, col: 0], items}
  defp qq_atom(a) when is_atom(a), do: {:literal, [subtype: :symbol, line: 0, col: 0], a}
  defp qq_lit(subtype, value), do: {:literal, [subtype: subtype, line: 0, col: 0], value}

  # -- expansion context -----------------------------------------------------

  @context_field "context"

  @doc """
  The field a computed rule's derived record carries in addition to its holes.

  A Tier-3 elab is otherwise blind to where it was invoked, so a rule with no
  holes (`beam_ops self`) would see nothing at all. The trailing field carries
  the reflected expansion context; a rule that declares a hole of the same name
  keeps its hole (and `MacroValidate` reports the collision).
  """
  @spec record_fields([String.t()]) :: [String.t()]
  def record_fields(syntax_fields), do: Enum.uniq(syntax_fields ++ [@context_field])

  @doc "The reserved derived-record field name."
  @spec context_field() :: String.t()
  def context_field, do: @context_field

  @doc """
  Reflect a macro's expansion context — the callback a use-site sits inside —
  as an ordinary `Std.Syntax` value. `nil` (an ordinary, non-callback use-site)
  reflects as `Raw(SOpaque)`, the same way any absent value does, so the elab's
  field is total.
  """
  @spec context_syntax(map() | nil) :: repr()
  def context_syntax(nil), do: {:syn_raw, :s_opaque}

  def context_syntax(context) when is_map(context) do
    attrs = for {key, value} <- Enum.sort(context), is_atom(key), do: {key, synlit(value)}
    {:syn_node, :callback_context, attrs, []}
  end

  @doc "Attach a reflected expansion context to a macro input's attributes."
  @spec with_context(repr(), map() | nil) :: repr()
  def with_context(repr, nil), do: repr

  def with_context({:syn_node, tag, attrs, kids}, context) when is_map(context),
    do: {:syn_node, tag, attrs ++ [{:expansion_context, {:s_syntax, context_syntax(context)}}], kids}

  def with_context(repr, _context), do: repr

  # Preserve source coordinates under dedicated mirror keys. They are not
  # semantic syntax attributes, but carrying them through reflection lets
  # generated-code diagnostics point back to authored syntax. Other semantic
  # meta values remain {key, synlit}; unrepresentable values become opaque.
  defp attrs(meta) when is_list(meta) do
    source_attrs =
      case Metadata.source_info(meta) do
        %SourceInfo{} = info -> [{@source_info_attr, info |> encode_source_value() |> synlit()}]
        _ -> []
      end

    source_attrs ++
      Enum.flat_map(meta, fn
        {:line, value} ->
          [{:source_line, synlit(value)}]

        {:col, value} ->
          [{:source_col, synlit(value)}]

        {key, value} ->
          if Metadata.diagnostic_key?(key), do: [], else: [{key, synlit(value)}]

        _ ->
          []
      end)
  end

  defp attrs(_), do: []

  defp pascal_case?(<<first::utf8, _rest::binary>>) when first in ?A..?Z, do: true
  defp pascal_case?(_), do: false

  defp synlit(v) when is_integer(v), do: {:s_int, v}
  defp synlit(v) when is_float(v), do: {:s_float, v}
  defp synlit(v) when is_binary(v), do: {:s_str, v}
  defp synlit(v) when is_boolean(v), do: {:s_bool, v}
  defp synlit(v) when is_atom(v), do: {:s_atom, v}
  defp synlit(v) when is_list(v), do: {:s_list, Enum.map(v, &synlit/1)}

  # A raw lexer Token, leaked into a macro input by a `delayed raw until dedent`
  # capture. Reflected by its content (type + value) only: source position is
  # excluded so the macro recursion guard (expansion_key/1) stays
  # position-insensitive, while two Tokens of different type or value still
  # reflect differently and are not conflated. A struct is a map, so this MUST
  # precede the plain-map clause below.
  defp synlit(%Cure.Compiler.Token{type: type, value: value}),
    do: {:s_list, [{:s_atom, type}, synlit(value)]}

  # A meta value that is a plain Elixir map (e.g. an `interface`'s
  # `defaults:` table, name -> default-method-body AST -- see
  # parse_interface/1). Representable losslessly as a list of key/value
  # synlit pairs; order is not semantically meaningful for a lookup table.
  # Structs are excluded — they are not plain lookup tables and are not
  # Enumerable (see the Token clause above).
  defp synlit(v) when is_map(v) and not is_struct(v),
    do: {:s_map, Enum.map(v, fn {k, val} -> {synlit(k), synlit(val)} end)}

  # A meta value that is itself a full AST node (e.g. a binary-segment
  # `size(expr)`/`unit(n)` specifier — see parse_bin_segment/1) rather than a
  # plain scalar. Representable losslessly by recursing through to_syntax, so
  # it does not need to fall back to :s_opaque like a genuinely irreducible
  # native term (e.g. a compiled regex).
  defp synlit({tag, meta, _} = v) when is_atom(tag) and is_list(meta), do: {:s_syntax, to_syntax(v)}

  defp synlit(_), do: :s_opaque

  # -- from_syntax: repr -> parser AST ---------------------------------------

  @spec from_syntax(repr) :: tuple()
  def from_syntax({:syn_node, :function_def, attrs, kids}) do
    attrs = materialize_identifier_name(attrs)
    {:function_def, from_attrs(attrs), Enum.map(kids, &from_syntax/1)}
  end

  def from_syntax({:syn_node, tag, attrs, kids}) do
    {tag, from_attrs(attrs), Enum.map(kids, &from_syntax/1)}
  end

  # Caller scope is an expansion intent, not a scope understood by ordinary
  # elaboration. Consume it at this boundary while retaining the reflected
  # marker for macros that inspect the syntax value before emission.
  def from_syntax({:syn_leaf, :variable, attrs, {:s_str, name}}) do
    meta = from_attrs(attrs)

    meta =
      if Keyword.get(meta, :scope) == :caller,
        do: Keyword.put(meta, :scope, :local),
        else: meta

    {:variable, meta, name}
  end

  def from_syntax({:syn_leaf, tag, attrs, lit}) do
    {tag, from_attrs(attrs), from_synlit(lit)}
  end

  def from_syntax({:syn_raw, lit}), do: from_synlit(lit)

  def from_syntax({:syn_quoted, repr}), do: {:quoted_syntax, [], [from_syntax(repr)]}

  def from_syntax({:syn_failure, name, args}),
    do: {:macro_failure, name, Enum.map(args, &from_syntax/1)}

  defp materialize_identifier_name(attrs) do
    source = Keyword.get(attrs, :name_from_identifier)
    transform = Keyword.get(attrs, :identifier_transform)

    name =
      case source do
        {:s_syntax, {:syn_leaf, _tag, _source_attrs, {:s_str, value}}} ->
          value

        {:s_syntax, {:syn_node, _tag, source_attrs, _kids}} ->
          case Keyword.get(source_attrs, :name) do
            {:s_str, value} -> value
            _ -> nil
          end

        _ ->
          nil
      end

    transformed =
      case {name, transform} do
        {value, {:s_atom, :lower_initial}} when is_binary(value) -> lower_initial(value)
        {value, _} when is_binary(value) -> value
        _ -> nil
      end

    attrs = Keyword.drop(attrs, [:name_from_identifier, :identifier_transform])
    if transformed, do: Keyword.put(attrs, :name, {:s_str, transformed}), else: attrs
  end

  defp lower_initial(<<first::utf8, rest::binary>>), do: String.downcase(<<first::utf8>>) <> rest
  defp lower_initial(""), do: ""

  defp from_attrs(attrs) do
    {encoded_source_info, attrs} = Keyword.pop(attrs, @source_info_attr)

    meta =
      for {key, lit} <- attrs, key not in [:pascal_case, :constructor_key, :variable_name] do
        case key do
          :source_line -> {:line, from_synlit(lit)}
          :source_col -> {:col, from_synlit(lit)}
          _ -> {key, from_synlit(lit)}
        end
      end

    case encoded_source_info do
      nil ->
        meta

      source_info ->
        case source_info |> from_synlit() |> decode_source_value() do
          %SourceInfo{} = info -> Keyword.put(meta, :source_info, info)
          _ -> meta
        end
    end
  end

  defp encode_source_value(%SourceInfo{} = info) do
    entries =
      info
      |> Map.from_struct()
      |> Enum.reject(fn {_key, value} -> value in [nil, [], %{}] end)
      |> Enum.sort_by(fn {key, _value} -> key end)
      |> Enum.map(fn {key, value} -> [key, encode_source_value(value)] end)

    [@source_info_tag, entries]
  end

  defp encode_source_value(%Span{} = span) do
    [
      @span_tag,
      encode_source_value(span.source_id),
      encode_source_value(span.path),
      span.start_byte,
      span.end_byte,
      span.start_line,
      span.start_column,
      span.end_line,
      span.end_column
    ]
  end

  defp encode_source_value(%ProvenanceFrame{} = frame) do
    [
      @provenance_tag,
      frame.kind,
      encode_source_value(frame.name),
      encode_source_value(frame.invocation),
      encode_source_value(frame.definition),
      encode_source_value(frame.generated),
      encode_source_value(frame.parent)
    ]
  end

  defp encode_source_value(map) when is_map(map) do
    entries =
      map
      |> Enum.sort_by(fn {key, _value} -> inspect(key) end)
      |> Enum.map(fn {key, value} -> [encode_source_value(key), encode_source_value(value)] end)

    [@map_tag, entries]
  end

  defp encode_source_value(list) when is_list(list), do: [@list_tag, Enum.map(list, &encode_source_value/1)]

  defp encode_source_value(tuple) when is_tuple(tuple),
    do: [@tuple_tag, tuple |> Tuple.to_list() |> Enum.map(&encode_source_value/1)]

  defp encode_source_value(value), do: value

  defp decode_source_value([@source_info_tag, entries]) when is_list(entries) do
    fields = Map.new(entries, fn [key, value] -> {key, decode_source_value(value)} end)
    struct(SourceInfo, fields)
  end

  defp decode_source_value([
         @span_tag,
         source_id,
         path,
         start_byte,
         end_byte,
         start_line,
         start_column,
         end_line,
         end_column
       ]) do
    %Span{
      source_id: decode_source_value(source_id),
      path: decode_source_value(path),
      start_byte: start_byte,
      end_byte: end_byte,
      start_line: start_line,
      start_column: start_column,
      end_line: end_line,
      end_column: end_column
    }
  end

  defp decode_source_value([@provenance_tag, kind, name, invocation, definition, generated, parent]) do
    %ProvenanceFrame{
      kind: kind,
      name: decode_source_value(name),
      invocation: decode_source_value(invocation),
      definition: decode_source_value(definition),
      generated: decode_source_value(generated),
      parent: decode_source_value(parent)
    }
  end

  defp decode_source_value([@map_tag, entries]) when is_list(entries) do
    Map.new(entries, fn [key, value] -> {decode_source_value(key), decode_source_value(value)} end)
  end

  defp decode_source_value([@list_tag, values]) when is_list(values),
    do: Enum.map(values, &decode_source_value/1)

  defp decode_source_value([@tuple_tag, values]) when is_list(values),
    do: values |> Enum.map(&decode_source_value/1) |> List.to_tuple()

  defp decode_source_value(value), do: value

  defp from_synlit({:s_int, n}), do: n
  defp from_synlit({:s_char, n}), do: n
  defp from_synlit({:s_float, f}), do: f
  defp from_synlit({:s_str, s}), do: s
  defp from_synlit({:s_bool, b}), do: b
  defp from_synlit({:s_atom, a}), do: a
  defp from_synlit({:s_list, items}), do: Enum.map(items, &from_synlit/1)
  defp from_synlit({:s_syntax, r}), do: from_syntax(r)

  defp from_synlit({:s_map, pairs}),
    do: Map.new(pairs, fn {k, v} -> {from_synlit(k), from_synlit(v)} end)

  defp from_synlit(:s_opaque), do: nil

  # -- mirror repr <-> Core Std.Syntax values -------------------------------

  @doc "Encode the Elixir mirror representation as a closed Core value."
  @spec to_core(repr()) :: Cure.Core.Term.t()
  def to_core({:syn_node, tag, attrs, kids}),
    do: ctor(:Node, [atom(tag), to_core_attrs(attrs), to_core_list(Enum.map(kids, &to_core/1))])

  def to_core({:syn_leaf, tag, attrs, lit}),
    do: ctor(:Leaf, [atom(tag), to_core_attrs(attrs), to_core_synlit(lit)])

  def to_core({:syn_raw, lit}), do: ctor(:Raw, [to_core_synlit(lit)])

  def to_core({:syn_quoted, syntax}), do: ctor(:Quoted, [to_core(syntax)])

  def to_core({:syn_failure, name, args}),
    do: ctor(:Failure, [atom(name), to_core_list(Enum.map(args, &to_core/1))])

  @doc """
  Encode the ordered children of a macro input as a derived syntax record.

  The record's fields are the rule's holes followed by the reserved `context`
  field (`record_fields/1`), so the encoded constructor carries one argument per
  hole plus the reflected expansion context. A rule that declares its own
  `context` hole owns the name, and no extra argument is appended.
  """
  @spec to_core_record(String.t() | atom(), [String.t()], repr()) :: Cure.Core.Term.t()
  def to_core_record(type_name, syntax_fields, repr),
    do: to_core_record(type_name, syntax_fields, [], repr, %{}, true)

  @spec to_core_record(String.t() | atom(), [String.t()], [String.t()], repr()) :: Cure.Core.Term.t()
  def to_core_record(type_name, syntax_fields, repeated_fields, repr),
    do: to_core_record(type_name, syntax_fields, repeated_fields, repr, %{}, true)

  @spec to_core_record(String.t() | atom(), [String.t()], [String.t()], repr(), map()) :: Cure.Core.Term.t()
  def to_core_record(type_name, syntax_fields, repeated_fields, repr, field_types),
    do: to_core_record(type_name, syntax_fields, repeated_fields, repr, field_types, true)

  @doc "Encode a nested syntax record without the reserved expansion context field."
  @spec to_core_record_without_context(String.t() | atom(), [String.t()], [String.t()], repr()) ::
          Cure.Core.Term.t()
  def to_core_record_without_context(type_name, syntax_fields, repeated_fields, repr),
    do: to_core_record(type_name, syntax_fields, repeated_fields, repr, %{}, false)

  @spec to_core_record_without_context(String.t() | atom(), [String.t()], [String.t()], repr(), map()) ::
          Cure.Core.Term.t()
  def to_core_record_without_context(type_name, syntax_fields, repeated_fields, repr, field_types),
    do: to_core_record(type_name, syntax_fields, repeated_fields, repr, field_types, false)

  defp to_core_record(
         type_name,
         syntax_fields,
         repeated_fields,
         {:syn_node, _tag, attrs, kids},
         field_types,
         include_context?
       ) do
    name = if is_binary(type_name), do: String.to_atom(type_name), else: type_name

    args =
      syntax_fields
      |> Enum.zip(kids)
      |> Enum.map(&to_core_record_field(&1, repeated_fields, field_types))

    args =
      if not include_context? or @context_field in syntax_fields,
        do: args,
        else: args ++ [to_core(context_attr(attrs))]

    {:ctor, name, args}
  end

  defp to_core_record(_type_name, _syntax_fields, _repeated_fields, repr, _field_types, _include_context?),
    do: to_core(repr)

  defp to_core_record_field({field, kid}, repeated_fields, field_types) do
    case Map.get(field_types, field) do
      {:optional, inner} ->
        option_kid(kid, inner, repeated_fields, field_types)

      field_type ->
        encode_core_record_field(kid, field_type, repeated_fields, field_types, field)
    end
  end

  defp encode_core_record_field(kid, {:record, nested_name, nested_fields}, repeated_fields, _field_types, field) do
    nested_repeated =
      nested_fields
      |> Enum.filter(&(&1.cardinality in [:repeated, :one_or_more]))
      |> Enum.map(& &1.name)

    encode = fn item ->
      to_core_record(
        nested_name,
        Enum.map(nested_fields, & &1.name),
        nested_repeated,
        item,
        family_field_types(nested_fields),
        false
      )
    end

    if field in repeated_fields do
      kid |> nested_record_items() |> Enum.map(encode) |> to_core_list()
    else
      encode.(kid)
    end
  end

  defp encode_core_record_field(kid, {:primitive, shape}, repeated_fields, _field_types, field) do
    if field in repeated_fields, do: to_core_primitive_list(kid, shape), else: to_core_primitive(kid, shape)
  end

  defp encode_core_record_field(kid, :syntax_list, _repeated_fields, _field_types, _field),
    do: to_core_syntax_list(kid)

  defp encode_core_record_field(kid, _field_type, repeated_fields, _field_types, field) do
    if field in repeated_fields, do: to_core_syntax_list(kid), else: to_core(kid)
  end

  defp nested_record_items({:syn_raw, {:s_list, [{:s_list, items}]}}), do: Enum.map(items, &nested_record_item/1)
  defp nested_record_items({:syn_raw, {:s_list, items}}), do: Enum.map(items, &nested_record_item/1)
  defp nested_record_items(item), do: [item]

  defp nested_record_item({:s_syntax, repr}), do: repr
  defp nested_record_item(lit), do: {:syn_raw, lit}

  defp option_kid({:syn_leaf, :option_none, _attrs, :s_opaque}, _inner, _repeated_fields, _field_types),
    do: {:ctor, option_ctor(:None), []}

  defp option_kid({:syn_node, :option_some, _attrs, [value]}, inner, repeated_fields, field_types),
    do: {:ctor, option_ctor(:Some), [encode_core_record_field(value, inner, repeated_fields, field_types, nil)]}

  defp option_kid(kid, inner, repeated_fields, field_types),
    do: {:ctor, option_ctor(:Some), [encode_core_record_field(kid, inner, repeated_fields, field_types, nil)]}

  defp option_ctor(name), do: Cure.Elab.Name.qualify("Std.Option", name)

  @doc "Build field metadata used to encode structured family records."
  @spec family_field_types([map()]) :: map()
  def family_field_types(fields) when is_list(fields) do
    Map.new(fields, fn field ->
      base =
        case Map.get(field, :grammar) do
          %{name: name, fields: fields} when is_atom(name) ->
            {:record, name, fields}

          %{name: name, fields: fields} ->
            {:record, Cure.Compiler.MacroFamily.syntax_type(name), fields}

          _ ->
            case field.shape do
              shape when shape in ["Int", "Float", "Atom", "Bool"] -> {:primitive, shape}
              "Parameters" -> :syntax_list
              _ -> :syntax
            end
        end

      value = if field.cardinality == :optional, do: {:optional, base}, else: base
      {field.name, value}
    end)
  end

  # The parser keeps one child slot per grammar field, so a repeated field is
  # represented as an outer one-element list containing the captured values.
  # Unwrap that field slot before constructing the reflected Cure list.
  defp to_core_syntax_list({:syn_raw, {:s_list, [{:s_list, items}]}}) do
    to_core_list(Enum.map(items, &to_core_syntax_item/1))
  end

  defp to_core_syntax_list({:syn_raw, {:s_list, items}}) do
    to_core_list(Enum.map(items, &to_core_syntax_item/1))
  end

  defp to_core_syntax_list(repr), do: to_core_list([to_core(repr)])

  defp to_core_syntax_item({:s_syntax, repr}), do: to_core(repr)
  defp to_core_syntax_item(lit), do: to_core({:syn_raw, lit})

  defp to_core_primitive_list({:syn_raw, {:s_list, [{:s_list, items}]}}, shape),
    do: to_core_list(Enum.map(items, fn item -> to_core_primitive({:syn_raw, item}, shape) end))

  defp to_core_primitive_list({:syn_raw, {:s_list, items}}, shape),
    do: to_core_list(Enum.map(items, fn item -> to_core_primitive({:syn_raw, item}, shape) end))

  defp to_core_primitive_list(repr, shape), do: to_core_list([to_core_primitive(repr, shape)])

  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_int, value}}, "Int"), do: {:int_lit, value}
  defp to_core_primitive({:syn_raw, {:s_int, value}}, "Int"), do: {:int_lit, value}
  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_float, value}}, "Float"), do: {:float_lit, value}
  defp to_core_primitive({:syn_raw, {:s_float, value}}, "Float"), do: {:float_lit, value}
  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_atom, value}}, "Atom"), do: {:atom_lit, value}
  defp to_core_primitive({:syn_raw, {:s_atom, value}}, "Atom"), do: {:atom_lit, value}

  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_bool, true}}, "Bool"), do: {:ctor, :True, []}
  defp to_core_primitive({:syn_leaf, :literal, _attrs, {:s_bool, false}}, "Bool"), do: {:ctor, :False, []}
  defp to_core_primitive({:syn_raw, {:s_bool, true}}, "Bool"), do: {:ctor, :True, []}
  defp to_core_primitive({:syn_raw, {:s_bool, false}}, "Bool"), do: {:ctor, :False, []}
  defp to_core_primitive({:syn_raw, {:s_syntax, repr}}, shape), do: to_core_primitive(repr, shape)

  defp to_core_primitive(repr, _shape), do: to_core(repr)

  @doc "Encode a literal capture according to a primitive family shape."
  @spec to_core_primitive_value(repr(), String.t()) :: Cure.Core.Term.t()
  def to_core_primitive_value(repr, shape), do: to_core_primitive(repr, shape)

  defp context_attr(attrs) do
    case List.keyfind(attrs, :expansion_context, 0) do
      {:expansion_context, {:s_syntax, repr}} -> repr
      _ -> {:syn_raw, :s_opaque}
    end
  end

  @doc "Decode a normalized Core value of Std.Syntax into the mirror representation."
  @spec from_core(Cure.Core.Term.t()) :: repr() | {:error, term()}
  def from_core(term), do: decode_core(canonicalize_core(term))

  @doc """
  Validate syntax that is about to cross from macro evaluation into elaboration.

  `Std.Syntax.Raw` deliberately permits construction without semantic checks, but
  raw and quoted values are reflection forms rather than executable expansion
  nodes. Keeping this boundary here means malformed advanced syntax gets a
  deterministic macro diagnostic instead of reaching an elaborator catch-all or
  causing a host exception. `Failure` is intentionally accepted because the
  legacy direct-Syntax failure protocol decodes it as an author diagnostic.
  """
  @spec validate_expansion(repr()) :: :ok | {:error, term()}
  def validate_expansion(repr), do: validate_expansion_node(repr, [])

  @doc "Decode the source-level MacroResult wrapper, if present."
  @spec from_core_macro_result(Cure.Core.Term.t()) ::
          {:expanded, repr()}
          | {:rejected, [repr()]}
          | :not_macro_result
          | {:error, term()}
  def from_core_macro_result(term) do
    case canonicalize_core(term) do
      {:ctor, :"Std.Syntax#Expanded", [syntax]} ->
        case from_core(syntax) do
          {:error, _} = error -> error
          repr -> {:expanded, repr}
        end

      {:ctor, :"Std.Syntax#Rejected", [diagnostics]} ->
        case decode_macro_diagnostics(diagnostics) do
          {:ok, values} -> {:rejected, values}
          error -> error
        end

      {:ctor, :"Std.Result#Ok", [syntax]} ->
        case from_core(syntax) do
          {:error, _} = error -> error
          repr -> {:expanded, repr}
        end

      {:ctor, :"Std.Result#Error", [diagnostic]} ->
        case decode_macro_diagnostics(diagnostic) do
          {:ok, values} -> {:rejected, values}
          error -> error
        end

      _ ->
        :not_macro_result
    end
  end

  @doc """
  Decode the erased BEAM representation of `Std.Syntax`.

  This is the runtime twin of `from_core/1`. Computed macros normally use the
  bounded Core normalizer, while an already-compiled macro may be executed as
  an optimization. Both paths cross the same mirror representation before
  generated syntax is accepted.
  """
  @spec from_runtime(term()) :: repr() | {:error, term()}
  def from_runtime({:Node, tag, attrs, kids}) when is_atom(tag) and is_list(kids) do
    with {:ok, attrs} <- from_runtime_attrs(attrs),
         {:ok, kids} <- map_results(kids, &from_runtime/1),
         true <- Enum.all?(kids, &syntax_repr?/1) do
      {:syn_node, tag, attrs, kids}
    else
      _ -> {:error, {:invalid_runtime_syntax_node, attrs, kids}}
    end
  end

  def from_runtime({:Leaf, tag, attrs, lit}) when is_atom(tag) do
    with {:ok, attrs} <- from_runtime_attrs(attrs),
         {:ok, lit} <- from_runtime_synlit(lit) do
      {:syn_leaf, tag, attrs, lit}
    else
      _ -> {:error, {:invalid_runtime_syntax_leaf, tag}}
    end
  end

  def from_runtime({:Raw, lit}) do
    case from_runtime_synlit(lit) do
      {:ok, decoded} -> {:syn_raw, decoded}
      error -> error
    end
  end

  def from_runtime({:Quoted, syntax}) do
    case from_runtime(syntax) do
      {:error, _} = error -> error
      decoded -> {:syn_quoted, decoded}
    end
  end

  def from_runtime({:Failure, name, args}) when is_atom(name) and is_list(args) do
    with {:ok, args} <- map_results(args, &from_runtime/1),
         true <- Enum.all?(args, &syntax_repr?/1) do
      {:syn_failure, name, args}
    else
      _ -> {:error, {:invalid_runtime_syntax_failure, name}}
    end
  end

  def from_runtime(other), do: {:error, {:unsupported_runtime_syntax, other}}

  @doc "Decode the erased BEAM representation of a source-level `MacroResult`."
  @spec from_runtime_macro_result(term()) ::
          {:expanded, repr()}
          | {:rejected, [repr()]}
          | :not_macro_result
          | {:error, term()}
  def from_runtime_macro_result({:Expanded, syntax}) do
    case from_runtime(syntax) do
      {:error, _} = error -> error
      repr -> {:expanded, repr}
    end
  end

  def from_runtime_macro_result({:Rejected, diagnostics}) when is_list(diagnostics) do
    with {:ok, diagnostics} <- map_results(diagnostics, &from_runtime/1),
         true <- Enum.all?(diagnostics, &syntax_repr?/1) do
      {:rejected, diagnostics}
    else
      _ -> {:error, :invalid_runtime_macro_diagnostics}
    end
  end

  def from_runtime_macro_result(_), do: :not_macro_result

  defp from_runtime_attrs(attrs) when is_list(attrs) do
    map_results(attrs, fn
      {:KV, key, lit} when is_atom(key) ->
        with {:ok, lit} <- from_runtime_synlit(lit), do: {key, lit}

      _ ->
        {:error, :invalid_runtime_syntax_attr}
    end)
  end

  defp from_runtime_attrs(_), do: {:error, :invalid_runtime_syntax_attrs}

  defp from_runtime_synlit({:SInt, n}) when is_integer(n), do: {:ok, {:s_int, n}}
  defp from_runtime_synlit({:SChar, n}) when is_integer(n) and n >= 0 and n <= 0x10FFFF, do: {:ok, {:s_char, n}}
  defp from_runtime_synlit({:SFloat, f}) when is_float(f), do: {:ok, {:s_float, f}}

  defp from_runtime_synlit({:SStr, string}) do
    with {:String, chars} when is_list(chars) <- string,
         true <- Enum.all?(chars, &(is_integer(&1) and &1 >= 0)) do
      try do
        {:ok, {:s_str, List.to_string(chars)}}
      rescue
        ArgumentError -> {:error, :invalid_runtime_syntax_string}
      end
    else
      _ -> {:error, :invalid_runtime_syntax_string}
    end
  end

  defp from_runtime_synlit({:SBool, value}) when is_boolean(value), do: {:ok, {:s_bool, value}}
  defp from_runtime_synlit({:SAtom, value}) when is_atom(value), do: {:ok, {:s_atom, value}}

  defp from_runtime_synlit({:SList, values}) when is_list(values) do
    with {:ok, values} <- map_results(values, &from_runtime_synlit/1),
         do: {:ok, {:s_list, values}}
  end

  defp from_runtime_synlit({:SSyntax, syntax}) do
    case from_runtime(syntax) do
      {:error, _} = error -> error
      decoded -> {:ok, {:s_syntax, decoded}}
    end
  end

  defp from_runtime_synlit({:SMap, pairs}) when is_list(pairs) do
    with {:ok, pairs} <- map_results(pairs, &from_runtime_pair/1),
         do: {:ok, {:s_map, pairs}}
  end

  defp from_runtime_synlit(:SOpaque), do: {:ok, :s_opaque}
  defp from_runtime_synlit(_), do: {:error, :invalid_runtime_syntax_literal}

  defp from_runtime_pair({:SPair, key, value}) do
    with {:ok, key} <- from_runtime_synlit(key),
         {:ok, value} <- from_runtime_synlit(value),
         do: {key, value}
  end

  defp from_runtime_pair(_), do: {:error, :invalid_runtime_syntax_pair}

  defp decode_macro_diagnostics(value) do
    case from_core(value) do
      {:error, _} ->
        with {:ok, diagnostics} <- from_core_list(value),
             {:ok, diagnostics} <- map_results(diagnostics, &from_core/1),
             true <- Enum.all?(diagnostics, &syntax_repr?/1) do
          {:ok, diagnostics}
        else
          _ -> {:error, :invalid_macro_diagnostics}
        end

      repr when is_tuple(repr) ->
        if syntax_repr?(repr), do: {:ok, [repr]}, else: {:error, :invalid_macro_diagnostic}
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Node", [{:atom_lit, tag}, attrs, kids]}) do
    with {:ok, attrs} <- from_core_attrs(attrs),
         {:ok, kids} <- from_core_list(kids),
         {:ok, kids} <- map_results(kids, &from_core/1),
         true <- Enum.all?(kids, &syntax_repr?/1) do
      {:syn_node, tag, attrs, kids}
    else
      _ -> {:error, {:invalid_syntax_node, attrs, kids}}
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Leaf", [{:atom_lit, tag}, attrs, lit]}) do
    with {:ok, attrs} <- from_core_attrs(attrs),
         {:ok, lit} <- from_core_synlit(lit) do
      {:syn_leaf, tag, attrs, lit}
    else
      _ -> {:error, {:invalid_syntax_leaf, tag}}
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Raw", [lit]}) do
    case from_core_synlit(lit) do
      {:ok, lit} -> {:syn_raw, lit}
      error -> error
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Quoted", [syntax]}) do
    case from_core(syntax) do
      {:error, _} = error -> error
      syntax -> {:syn_quoted, syntax}
    end
  end

  defp decode_core({:ctor, :"Std.Syntax#Failure", [{:atom_lit, name}, args]}) do
    with {:ok, args} <- from_core_list(args),
         {:ok, args} <- map_results(args, &from_core/1),
         true <- Enum.all?(args, &syntax_repr?/1) do
      {:syn_failure, name, args}
    else
      _ -> {:error, {:invalid_syntax_failure, name}}
    end
  end

  defp decode_core(other), do: {:error, {:unsupported_syntax_core, other}}

  defp validate_expansion_node({:syn_node, tag, attrs, kids}, path)
       when is_atom(tag) and is_list(attrs) and is_list(kids) do
    with :ok <- validate_attrs(attrs, path),
         :ok <- validate_expansion_children(kids, path) do
      :ok
    end
  end

  defp validate_expansion_node({:syn_leaf, tag, attrs, lit}, path)
       when is_atom(tag) and is_list(attrs) do
    with :ok <- validate_attrs(attrs, path),
         :ok <- validate_synlit(lit, path) do
      :ok
    end
  end

  defp validate_expansion_node({:syn_failure, name, args}, path) when is_atom(name) and is_list(args),
    do: validate_reflected_children(args, [{:failure_arguments} | path])

  defp validate_expansion_node({:syn_raw, _lit}, path),
    do: {:error, {:raw_syntax_in_expansion, path}}

  defp validate_expansion_node({:syn_quoted, _syntax}, path),
    do: {:error, {:quoted_syntax_in_expansion, path}}

  defp validate_expansion_node(_other, path),
    do: {:error, {:malformed_expansion_syntax, path}}

  defp validate_expansion_children(children, path) do
    children
    |> Enum.with_index()
    |> Enum.reduce_while(:ok, fn {child, index}, :ok ->
      case validate_expansion_node(child, [{:child, index} | path]) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp validate_attrs(attrs, path) do
    attrs
    |> Enum.with_index()
    |> Enum.reduce_while(:ok, fn
      {{key, value}, index}, :ok when is_atom(key) ->
        case validate_synlit(value, [{:attribute, key, index} | path]) do
          :ok -> {:cont, :ok}
          {:error, _} = error -> {:halt, error}
        end

      {_attribute, index}, :ok ->
        {:halt, {:error, {:malformed_expansion_attribute, [{:attribute, index} | path]}}}
    end)
  end

  defp validate_synlit({:s_int, value}, _path) when is_integer(value), do: :ok
  defp validate_synlit({:s_char, value}, _path) when is_integer(value) and value >= 0 and value <= 0x10FFFF, do: :ok
  defp validate_synlit({:s_float, value}, _path) when is_float(value), do: :ok
  defp validate_synlit({:s_str, value}, _path) when is_binary(value), do: :ok
  defp validate_synlit({:s_bool, value}, _path) when is_boolean(value), do: :ok
  defp validate_synlit({:s_atom, value}, _path) when is_atom(value), do: :ok

  defp validate_synlit({:s_list, values}, path) when is_list(values) do
    Enum.reduce_while(values, :ok, fn value, :ok ->
      case validate_synlit(value, [{:list_item} | path]) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp validate_synlit({:s_map, pairs}, path) when is_list(pairs) do
    Enum.reduce_while(pairs, :ok, fn
      {key, value}, :ok ->
        with :ok <- validate_synlit(key, [{:map_key} | path]),
             :ok <- validate_synlit(value, [{:map_value} | path]) do
          {:cont, :ok}
        else
          {:error, _} = error -> {:halt, error}
        end

      _pair, :ok ->
        {:halt, {:error, {:malformed_expansion_map, path}}}
    end)
  end

  defp validate_synlit(:s_opaque, _path), do: :ok

  defp validate_synlit({:s_syntax, syntax}, path),
    do: validate_reflected_node(syntax, [{:syntax_literal} | path])

  defp validate_synlit(_other, path),
    do: {:error, {:malformed_expansion_literal, path}}

  defp validate_reflected_node({:syn_node, tag, attrs, kids}, path)
       when is_atom(tag) and is_list(attrs) and is_list(kids) do
    with :ok <- validate_reflected_attrs(attrs, path),
         :ok <- validate_reflected_children(kids, path) do
      :ok
    end
  end

  defp validate_reflected_node({:syn_leaf, tag, attrs, lit}, path)
       when is_atom(tag) and is_list(attrs),
       do: validate_reflected_attrs(attrs, path) |> then(&validate_reflected_literal(&1, lit, path))

  defp validate_reflected_node({:syn_raw, lit}, path),
    do: validate_reflected_literal(:ok, lit, [{:raw_literal} | path])

  defp validate_reflected_node({:syn_quoted, syntax}, path),
    do: validate_reflected_node(syntax, [{:quoted_syntax} | path])

  defp validate_reflected_node({:syn_failure, name, args}, path) when is_atom(name) and is_list(args),
    do: validate_reflected_children(args, [{:failure_arguments} | path])

  defp validate_reflected_node(_other, path), do: {:error, {:malformed_reflected_syntax, path}}

  defp validate_reflected_children(children, path) do
    children
    |> Enum.with_index()
    |> Enum.reduce_while(:ok, fn {child, index}, :ok ->
      case validate_reflected_node(child, [{:child, index} | path]) do
        :ok -> {:cont, :ok}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp validate_reflected_attrs(attrs, path) do
    attrs
    |> Enum.with_index()
    |> Enum.reduce_while(:ok, fn
      {{key, value}, index}, :ok when is_atom(key) ->
        case validate_reflected_literal(:ok, value, [{:attribute, key, index} | path]) do
          :ok -> {:cont, :ok}
          {:error, _} = error -> {:halt, error}
        end

      {_attribute, index}, :ok ->
        {:halt, {:error, {:malformed_reflected_attribute, [{:attribute, index} | path]}}}
    end)
  end

  defp validate_reflected_literal(:ok, {:s_syntax, syntax}, path),
    do: validate_reflected_node(syntax, path)

  defp validate_reflected_literal(:ok, {:s_list, values}, path) when is_list(values),
    do: Enum.reduce_while(values, :ok, &validate_reflected_literal_item(&1, &2, path))

  defp validate_reflected_literal(:ok, {:s_map, pairs}, path) when is_list(pairs),
    do: Enum.reduce_while(pairs, :ok, &validate_reflected_pair(&1, &2, path))

  defp validate_reflected_literal(:ok, {:s_int, value}, _path) when is_integer(value), do: :ok

  defp validate_reflected_literal(:ok, {:s_char, value}, _path)
       when is_integer(value) and value >= 0 and value <= 0x10FFFF,
       do: :ok

  defp validate_reflected_literal(:ok, {:s_float, value}, _path) when is_float(value), do: :ok
  defp validate_reflected_literal(:ok, {:s_str, value}, _path) when is_binary(value), do: :ok
  defp validate_reflected_literal(:ok, {:s_bool, value}, _path) when is_boolean(value), do: :ok
  defp validate_reflected_literal(:ok, {:s_atom, value}, _path) when is_atom(value), do: :ok
  defp validate_reflected_literal(:ok, :s_opaque, _path), do: :ok
  defp validate_reflected_literal({:error, _} = error, _value, _path), do: error
  defp validate_reflected_literal(_result, _value, path), do: {:error, {:malformed_reflected_literal, path}}

  defp validate_reflected_literal_item(value, :ok, path),
    do: validate_reflected_literal(:ok, value, [{:list_item} | path]) |> reduce_validation()

  defp validate_reflected_pair({key, value}, :ok, path) do
    with :ok <- validate_reflected_literal(:ok, key, [{:map_key} | path]),
         :ok <- validate_reflected_literal(:ok, value, [{:map_value} | path]) do
      {:cont, :ok}
    else
      {:error, _} = error -> {:halt, error}
    end
  end

  defp validate_reflected_pair(_pair, :ok, path),
    do: {:halt, {:error, {:malformed_reflected_map, path}}}

  defp reduce_validation(:ok), do: {:cont, :ok}
  defp reduce_validation({:error, _} = error), do: {:halt, error}

  defp ctor(name, args), do: {:ctor, canonical_ctor(name), args}

  defp canonical_ctor(name) when name in [:True, :False],
    do: Cure.Elab.Name.qualify("Std.Bool", name)

  defp canonical_ctor(name) when name in [:Nil, :Cons],
    do: Cure.Elab.Name.qualify("Std.List", name)

  defp canonical_ctor(:String), do: Cure.Elab.Name.qualify("Std.String", :String)

  defp canonical_ctor(name), do: Cure.Elab.Name.qualify("Std.Syntax", name)

  defp canonicalize_core({:ctor, name, args}) when is_atom(name) and is_list(args) do
    base = Cure.Elab.Name.base(name) |> String.to_atom()
    canonical_name = if syntax_ctor?(base), do: canonical_ctor(base), else: name
    {:ctor, canonical_name, Enum.map(args, &canonicalize_core/1)}
  end

  defp canonicalize_core({:app, f, a}), do: {:app, canonicalize_core(f), canonicalize_core(a)}
  defp canonicalize_core({:lam, g, d, b}), do: {:lam, g, canonicalize_core(d), canonicalize_core(b)}
  defp canonicalize_core({:pi, g, d, c}), do: {:pi, g, canonicalize_core(d), canonicalize_core(c)}

  defp canonicalize_core({:data, n, ps, is}) when is_list(ps) and is_list(is),
    do: {:data, n, Enum.map(ps, &canonicalize_core/1), Enum.map(is, &canonicalize_core/1)}

  defp canonicalize_core(other), do: other

  defp syntax_ctor?(name),
    do:
      name in [
        :Node,
        :Leaf,
        :Raw,
        :Quoted,
        :Failure,
        :KV,
        :SInt,
        :SChar,
        :SFloat,
        :SStr,
        :SBool,
        :SAtom,
        :SList,
        :SSyntax,
        :SMap,
        :SOpaque,
        :SPair,
        :True,
        :False,
        :Nil,
        :Cons,
        :String
      ]

  defp atom(value), do: {:atom_lit, value}

  defp to_core_attrs(attrs),
    do: to_core_list(Enum.map(attrs, fn {key, lit} -> ctor(:KV, [atom(key), to_core_synlit(lit)]) end))

  defp to_core_list(items), do: Enum.reduce(Enum.reverse(items), ctor(:Nil, []), &ctor(:Cons, [&1, &2]))

  # `String` is nominal -- `rec String { characters: List(Char) }` -- so a `String`
  # value is the constructor wrapping its characters, one layer outside the list.
  # `SStr` is declared `SStr(String)`, and handing it the bare list instead type-
  # checks as `List(Char)`, which is a different type.
  defp to_core_string(s),
    do: ctor(:String, [to_core_list(Enum.map(String.to_charlist(s), &{:bounded_lit, &1}))])

  defp to_core_synlit({:s_int, n}), do: ctor(:SInt, [{:int_lit, n}])
  defp to_core_synlit({:s_char, n}), do: ctor(:SChar, [{:bounded_lit, n}])
  defp to_core_synlit({:s_float, f}), do: ctor(:SFloat, [{:float_lit, f}])

  defp to_core_synlit({:s_str, s}), do: ctor(:SStr, [to_core_string(s)])

  defp to_core_synlit({:s_bool, true}), do: ctor(:SBool, [ctor(:True, [])])
  defp to_core_synlit({:s_bool, false}), do: ctor(:SBool, [ctor(:False, [])])
  defp to_core_synlit({:s_atom, a}), do: ctor(:SAtom, [atom(a)])
  defp to_core_synlit({:s_list, items}), do: ctor(:SList, [to_core_list(Enum.map(items, &to_core_synlit/1))])
  defp to_core_synlit({:s_syntax, syntax}), do: ctor(:SSyntax, [to_core(syntax)])

  defp to_core_synlit({:s_map, pairs}) do
    values = Enum.map(pairs, fn {key, value} -> ctor(:SPair, [to_core_synlit(key), to_core_synlit(value)]) end)
    ctor(:SMap, [to_core_list(values)])
  end

  defp to_core_synlit(:s_opaque), do: ctor(:SOpaque, [])

  defp from_core_attrs(core) do
    with {:ok, entries} <- from_core_list(core),
         {:ok, attrs} <-
           map_results(entries, fn
             {:ctor, :"Std.Syntax#KV", [{:atom_lit, key}, lit]} ->
               with {:ok, lit} <- from_core_synlit(lit), do: {key, lit}

             _ ->
               {:error, :invalid_syntax_attr}
           end) do
      {:ok, attrs}
    else
      _ -> {:error, {:invalid_syntax_attrs, core}}
    end
  end

  defp from_core_list({:ctor, :"Std.List#Nil", []}), do: {:ok, []}

  defp from_core_list({:ctor, :"Std.List#Cons", [head, tail]}) do
    with {:ok, rest} <- from_core_list(tail), do: {:ok, [head | rest]}
  end

  defp from_core_list(_), do: {:error, :invalid_syntax_list}

  defp from_core_synlit({:ctor, :"Std.Syntax#SInt", [{:int_lit, n}]}), do: {:ok, {:s_int, n}}
  defp from_core_synlit({:ctor, :"Std.Syntax#SChar", [{:bounded_lit, n}]}), do: {:ok, {:s_char, n}}
  defp from_core_synlit({:ctor, :"Std.Syntax#SFloat", [{:float_lit, f}]}), do: {:ok, {:s_float, f}}

  # The `String` wrapper is unwrapped in the body rather than the head so that a
  # malformed payload still reports the specific `:invalid_syntax_string` verdict
  # instead of falling through to the catch-all `:invalid_syntax_literal`.
  defp from_core_synlit({:ctor, :"Std.Syntax#SStr", [string]}) do
    with {:ctor, :"Std.String#String", [chars]} <- string,
         {:ok, chars} <- from_core_list(chars),
         true <- Enum.all?(chars, &match?({:bounded_lit, n} when is_integer(n), &1)) do
      {:ok, {:s_str, chars |> Enum.map(fn {:bounded_lit, n} -> n end) |> List.to_string()}}
    else
      _ -> {:error, :invalid_syntax_string}
    end
  end

  defp from_core_synlit({:ctor, :"Std.Syntax#SBool", [{:ctor, :"Std.Bool#True", []}]}), do: {:ok, {:s_bool, true}}
  defp from_core_synlit({:ctor, :"Std.Syntax#SBool", [{:ctor, :"Std.Bool#False", []}]}), do: {:ok, {:s_bool, false}}
  defp from_core_synlit({:ctor, :"Std.Syntax#SAtom", [{:atom_lit, a}]}), do: {:ok, {:s_atom, a}}

  defp from_core_synlit({:ctor, :"Std.Syntax#SList", [items]}) do
    with {:ok, items} <- from_core_list(items),
         {:ok, items} <- map_results(items, &from_core_synlit/1) do
      {:ok, {:s_list, items}}
    end
  end

  defp from_core_synlit({:ctor, :"Std.Syntax#SSyntax", [syntax]}) do
    case from_core(syntax) do
      {:error, _} = error -> error
      syntax -> {:ok, {:s_syntax, syntax}}
    end
  end

  defp from_core_synlit({:ctor, :"Std.Syntax#SMap", [pairs]}) do
    with {:ok, pairs} <- from_core_list(pairs),
         {:ok, pairs} <- map_results(pairs, &from_core_pair/1) do
      {:ok, {:s_map, pairs}}
    end
  end

  defp from_core_synlit({:ctor, :"Std.Syntax#SOpaque", []}), do: {:ok, :s_opaque}
  defp from_core_synlit(_), do: {:error, :invalid_syntax_literal}

  defp from_core_pair({:ctor, :"Std.Syntax#SPair", [key, value]}) do
    with {:ok, key} <- from_core_synlit(key), {:ok, value} <- from_core_synlit(value), do: {key, value}
  end

  defp from_core_pair(_), do: {:error, :invalid_syntax_pair}

  defp syntax_repr?({:syn_node, _, _, _}), do: true
  defp syntax_repr?({:syn_leaf, _, _, _}), do: true
  defp syntax_repr?({:syn_raw, _}), do: true
  defp syntax_repr?({:syn_quoted, _}), do: true
  defp syntax_repr?({:syn_failure, _, _}), do: true
  defp syntax_repr?(_), do: false

  defp map_results(items, fun) do
    Enum.reduce_while(items, {:ok, []}, fn item, {:ok, acc} ->
      case fun.(item) do
        {:ok, value} -> {:cont, {:ok, [value | acc]}}
        {:error, _} = error -> {:halt, error}
        value -> {:cont, {:ok, [value | acc]}}
      end
    end)
    |> case do
      {:ok, values} -> {:ok, Enum.reverse(values)}
      error -> error
    end
  end
end
