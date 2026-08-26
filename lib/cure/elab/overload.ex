defmodule Cure.Elab.Overload do
  @moduledoc """
  Telescope alignment and type-directed pruning for applied overload sets.
  Written arguments are aligned independently against each candidate before
  bidirectional elaboration, so named-argument order never leaks into Core.
  This module is pure over an already-elaborated `Env`; it never rewrites Core
  and never touches the kernel/TCB.

  `resolve/5` remains the legacy helper for callers that already possess an
  aligned vector of inferred argument types. Ordinary applied calls use
  `align_candidates/5` followed by candidate-specific bidirectional checking.
  """

  alias Cure.Core.{Env, Grade}

  @type label :: String.t() | nil

  @doc """
  Align authored call arguments to a definition's present parameter telescope.

  Positional arguments fill the leftmost slots. Once a named argument appears,
  every following argument must be named; named arguments may otherwise be
  written in any order. The returned list is purely positional and is the only
  shape passed to Core construction.
  """
  @spec align(Env.t(), atom(), [term()], [label()] | nil, keyword()) ::
          {:ok, [term()]} | {:error, term()}
  def align(%Env{} = env, key, args, written, opts \\ []) do
    case Env.get_def(env, key) do
      %{type: pi} = def ->
        descriptors = present_labels(def, pi)
        opts = Keyword.put_new(opts, :parameter_spans, present_label_spans(key, pi))
        align_descriptors(key, descriptors, args, written, opts)

      _ ->
        {:ok, args}
    end
  end

  @doc "Align against an explicit descriptor vector (used by interface methods before dictionary dispatch)."
  def align_labels(key, descriptors, args, written, opts \\ []) do
    align_descriptors(key, descriptors, args, written, opts)
  end

  @doc "Return each overload candidate whose labels can be aligned, with its reordered arguments."
  @spec align_candidates(Env.t(), [atom()], [term()], [label()] | nil, keyword()) ::
          [{atom(), [term()]}] | {:error, term()}
  def align_candidates(%Env{} = env, candidates, args, written, opts \\ []) do
    results = Enum.map(candidates, &{&1, align(env, &1, args, written, opts)})

    aligned = for {key, {:ok, reordered}} <- results, do: {key, reordered}

    cond do
      aligned != [] ->
        aligned

      length(candidates) == 1 ->
        {_key, {:error, reason}} = hd(results)
        {:error, reason}

      true ->
        errors = for {key, {:error, reason}} <- results, do: %{candidate: key, reason: reason}

        variants =
          errors |> Enum.map(fn %{reason: {:named_argument_mismatch, variant, _}} -> variant end) |> Enum.uniq()

        variant = if length(variants) == 1, do: hd(variants), else: :ambiguous_label

        label =
          errors
          |> Enum.map(fn %{reason: {:named_argument_mismatch, _variant, details}} -> details.label end)
          |> Enum.uniq()
          |> case do
            [only] -> only
            _ -> nil
          end

        {:error,
         named_error(variant, nil, label, written, opts,
           candidates: candidates,
           candidate_errors: errors
         )}
    end
  end

  defp align_descriptors(key, descriptors, args, nil, opts) do
    supplied = Enum.take(descriptors, length(args))

    case Enum.find_index(supplied, &mandatory?/1) do
      nil ->
        {:ok, args}

      index ->
        {:error,
         named_error(:missing_label, key, descriptor_name(Enum.at(descriptors, index)), nil, opts,
           parameter_index: index,
           telescope: descriptors
         )}
    end
  end

  defp align_descriptors(key, descriptors, args, written, opts)
       when is_list(written) and length(args) == length(written) do
    case positional_after_named(written) do
      nil ->
        align_named(key, descriptors, args, written, opts)

      index ->
        {:error,
         named_error(:positional_after_named, key, nil, written, opts, argument_index: index, telescope: descriptors)}
    end
  end

  defp align_descriptors(_key, _descriptors, args, _written, _opts), do: {:ok, args}

  defp align_named(key, descriptors, args, written, opts) do
    positional_count = Enum.take_while(written, &is_nil/1) |> length()

    positional =
      args |> Enum.take(positional_count) |> Enum.with_index() |> Map.new(fn {arg, i} -> {i, {arg, :positional}} end)

    named = Enum.zip(Enum.drop(written, positional_count), Enum.drop(args, positional_count))

    with :ok <- reject_duplicate_written(key, named, written, opts, descriptors),
         {:ok, filled} <- place_named(key, named, positional, positional_count, descriptors, written, opts),
         :ok <- validate_filled_prefix(key, filled, descriptors, written, opts) do
      max_index = filled |> Map.keys() |> Enum.max(fn -> -1 end)
      {:ok, for(index <- 0..max_index, max_index >= 0, do: filled |> Map.fetch!(index) |> elem(0))}
    end
  end

  defp positional_after_named(labels) do
    labels
    |> Enum.with_index()
    |> Enum.reduce_while(false, fn
      {nil, index}, true -> {:halt, index}
      {nil, _index}, false -> {:cont, false}
      {_label, _index}, _seen -> {:cont, true}
    end)
    |> case do
      index when is_integer(index) -> index
      _ -> nil
    end
  end

  defp reject_duplicate_written(key, named, written, opts, descriptors) do
    labels = Enum.map(named, &elem(&1, 0))

    case Enum.find(Enum.frequencies(labels), fn {_label, count} -> count > 1 end) do
      {label, _} -> {:error, named_error(:duplicate_label, key, label, written, opts, telescope: descriptors)}
      nil -> :ok
    end
  end

  defp place_named(key, named, filled, positional_count, descriptors, written, opts) do
    Enum.reduce_while(named, {:ok, filled}, fn {label, arg}, {:ok, acc} ->
      all_matches = descriptor_matches(descriptors, label)
      available = Enum.reject(all_matches, &Map.has_key?(acc, &1))

      result =
        cond do
          all_matches == [] ->
            {:error, named_error(:unknown_label, key, label, written, opts, telescope: descriptors)}

          available == [] ->
            {:error, named_error(:duplicate_label, key, label, written, opts, telescope: descriptors)}

          length(available) > 1 ->
            {:error,
             named_error(:ambiguous_label, key, label, written, opts,
               parameter_indices: available,
               telescope: descriptors
             )}

          true ->
            [index] = available

            if index < positional_count do
              {:error,
               named_error(:duplicate_label, key, label, written, opts, parameter_index: index, telescope: descriptors)}
            else
              {:ok, Map.put(acc, index, {arg, {:named, label}})}
            end
        end

      case result do
        {:ok, next} -> {:cont, {:ok, next}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp validate_filled_prefix(key, filled, descriptors, written, opts) do
    max_index = filled |> Map.keys() |> Enum.max(fn -> -1 end)

    Enum.reduce_while(0..max_index, :ok, fn index, :ok ->
      case Map.get(filled, index) do
        nil ->
          {:halt,
           {:error,
            named_error(:missing_label, key, descriptor_name(Enum.at(descriptors, index)), written, opts,
              parameter_index: index,
              telescope: descriptors
            )}}

        {_arg, :positional} ->
          descriptor = Enum.at(descriptors, index)

          if mandatory?(descriptor) do
            {:halt,
             {:error,
              named_error(:missing_label, key, descriptor_name(descriptor), written, opts,
                parameter_index: index,
                telescope: descriptors
              )}}
          else
            {:cont, :ok}
          end

        {_arg, {:named, _label}} ->
          {:cont, :ok}
      end
    end)
  end

  defp descriptor_matches(descriptors, label) do
    descriptors
    |> Enum.with_index()
    |> Enum.flat_map(fn {descriptor, index} -> if descriptor_name(descriptor) == label, do: [index], else: [] end)
  end

  defp descriptor_name({:required, label}), do: label
  defp descriptor_name({:optional, name}), do: name

  defp named_error(variant, key, label, written, opts, extra) do
    {:named_argument_mismatch, variant,
     extra
     |> Map.new()
     |> Map.merge(%{
       key: key,
       label: label,
       written: written,
       argument_spans: Keyword.get(opts, :argument_spans, []),
       label_spans: Keyword.get(opts, :label_spans, []),
       parameter_spans: Keyword.get(opts, :parameter_spans, []) |> Enum.reject(&is_nil/1)
     })}
  end

  @spec resolve(Env.t(), atom(), [term()], [String.t() | nil] | nil, [atom()]) ::
          {:ok, atom()}
          | {:error, {:no_matching_overload, atom(), [term()]}}
          | {:error, {:ambiguous_overload, atom(), [String.t()]}}
  def resolve(%Env{} = env, bare, arg_types, written_labels, candidates) do
    survivors =
      Enum.filter(candidates, fn key ->
        case Env.get_def(env, key) do
          %{type: pi} = def ->
            labels_match?(present_labels(def, pi), written_labels) and
              params_match?(env, present_param_types(pi), arg_types)

          _ ->
            false
        end
      end)

    case survivors do
      [key] -> {:ok, key}
      [] -> {:error, {:no_matching_overload, bare, arg_types}}
      many -> {:error, {:ambiguous_overload, bare, owners(many)}}
    end
  end

  @doc "Whether already telescope-aligned argument types can inhabit one overload candidate."
  def types_match?(%Env{} = env, key, arg_types) do
    case Env.get_def(env, key) do
      %{type: pi} -> params_match?(env, present_param_types(pi), arg_types)
      _ -> false
    end
  end

  @doc "Owner names used in overload ambiguity diagnostics."
  def candidate_owners(keys), do: owners(keys)

  @doc "Semantic parameter signatures retained for no-match diagnostics."
  def candidate_signatures(%Env{} = env, keys) do
    Enum.flat_map(keys, fn key ->
      case Env.get_def(env, key) do
        %{type: pi} ->
          [
            %{
              id: key,
              owner: Cure.Elab.Name.owner(key),
              parameters: present_param_types(pi)
            }
          ]

        _ ->
          []
      end
    end)
  end

  @doc """
  Legacy declaration-order label check for callers that have not migrated to
  `align/5`. Ordinary calls use telescope alignment, including reordering. This
  helper only enforces mandatory labels position-wise: a mandatory (two-name)
  label must be written and match, while an optional (single-name) label may be
  omitted or written freely.

  Returns `:ok`, or `{:error, {:label_mismatch, key, declared_present, written}}`
  where both vectors are aligned to the present (non-erased) parameters. A key
  that names no def, or a def with no mandatory labels called without labels, is
  inert `:ok` — keeping every pre-Ph2 call unaffected.
  """
  @spec check_labels(Env.t(), atom(), [String.t() | nil] | nil) ::
          :ok | {:error, {:label_mismatch, atom(), [String.t() | nil], [String.t() | nil] | nil}}
  def check_labels(%Env{} = env, key, written) do
    case Env.get_def(env, key) do
      %{type: pi} = def ->
        declared = present_labels(def, pi)

        if single_labels_ok?(declared, written),
          do: :ok,
          else: {:error, {:label_mismatch, key, declared, written}}

      _ ->
        :ok
    end
  end

  # A lone target's present-param label descriptors versus what the caller wrote.
  # An unwritten call (`written == nil`) is legal only when no present parameter
  # carries a MANDATORY label — matching every pre-Ph2 def, whose present params
  # are all `{:optional, _}`. When labels ARE written, each position is checked by
  # `label_pos_ok?/2`: a mandatory label must be written identically; an optional
  # one may be omitted or written with the retained binder name (a label naming no
  # parameter is rejected). A length mismatch defers to the arity machinery rather
  # than double-diagnosing here (so `single_labels_ok?/2` and the pruning
  # `labels_match?/2` differ ONLY at that last clause).
  defp single_labels_ok?(declared, nil), do: not Enum.any?(declared, &mandatory?/1)

  defp single_labels_ok?(declared, written) when length(declared) == length(written) do
    Enum.zip(declared, written) |> Enum.all?(fn {d, w} -> label_pos_ok?(d, w) end)
  end

  defp single_labels_ok?(_declared, _written), do: true

  # A candidate's present-param label descriptors must agree with the labels the
  # caller actually wrote. Both vectors are aligned to the PRESENT (non-erased)
  # parameters — the same positions `present_param_types/1` prunes on and the same
  # positions the surface writes arguments for.
  #
  # An unwritten call (`written_labels == nil`, the whole common case) matches ONLY
  # a candidate with no mandatory present label — every pre-Ph2 def is
  # all-`{:optional, _}`, keeping Ph1 resolution unchanged. When labels are
  # written, each position is checked by `label_pos_ok?/2`: a mandatory external
  # label (`to dest`) matches only when the caller writes it; an optional
  # (single-name) label matches when omitted OR written with the parameter's own
  # binder name (`describe(x: 5)` for `fn describe(x: Int)` — the SAME call as
  # `describe(5)`, spec §3/§5). A written label naming NO parameter prunes the
  # candidate, and a length mismatch is a non-match (wrong arity for this member).
  defp labels_match?(declared_present, nil), do: not Enum.any?(declared_present, &mandatory?/1)

  defp labels_match?(declared_present, written) when length(declared_present) == length(written) do
    Enum.zip(declared_present, written) |> Enum.all?(fn {d, w} -> label_pos_ok?(d, w) end)
  end

  defp labels_match?(_declared_present, _written), do: false

  # Whether a parameter's label descriptor makes writing the label mandatory.
  defp mandatory?({:required, _label}), do: true
  defp mandatory?(_optional), do: false

  # Whether the label the caller wrote at one position (`w`, possibly `nil`) is
  # allowed by that parameter's descriptor. A mandatory label must be written
  # exactly; an optional one may be omitted or written with the parameter's own
  # binder name; an optional position whose name was not recorded stays lenient.
  defp label_pos_ok?({:required, label}, w), do: w == label
  defp label_pos_ok?({:optional, nil}, _w), do: true
  defp label_pos_ok?({:optional, name}, w), do: is_nil(w) or w == name

  defp params_match?(_env, ptypes, atypes) when length(ptypes) != length(atypes), do: false

  defp params_match?(env, ptypes, atypes) do
    Enum.all?(Enum.zip(ptypes, atypes), fn {p, a} ->
      # A polymorphic/dependent present param (one still mentioning a telescope
      # binder — e.g. `List(t)` under an erased `{t: Type}`, or `Vec(n)` under a
      # value `n`) cannot be decided by first-order conversion here, because the
      # binder is not yet instantiated to the argument. Conservatively KEEP such a
      # candidate rather than pruning it: this errs toward ambiguity (the caller
      # qualifies), never toward a silent wrong unique pick. A ground param is
      # decided by ordinary convertibility.
      mentions_var?(p) or Cure.Elab.TypeConv.convertible?(env, p, a)
    end)
  end

  # The PRESENT (non-erased) parameter domains of the stored Pi type, in order.
  # An erased leading implicit (`{t: Type}`, grade 0 — e.g. the `t` of a
  # polymorphic `Std.List#length : {t} -> List(t) -> Nat`) carries no runtime
  # argument and no inferred arg type to prune against, so it is dropped: the
  # present-param arity then matches the present-argument arity that
  # `map_present_args/4` produced. Value- and type-domains alike are kept when
  # present — NOT the `typealias_parameter_count` shape, whose `{:type, _level}`
  # guard would drop ordinary value-typed domains like `Meters`/`Grams`.
  defp present_param_types({:pi, grade, domain, codomain}) do
    rest = present_param_types(codomain)
    if Grade.present?(grade), do: [domain | rest], else: rest
  end

  defp present_param_types(_return), do: []

  # The label descriptors of a candidate's PRESENT parameters, in order — the
  # vector stored on the def record (telescope-aligned, full length), restricted
  # to the same non-erased positions `present_param_types/1` keeps. A def with no
  # stored vector defaults to `{:optional, nil}` at every position (lenient, no
  # mandatory label), so pre-Ph2 defs are unaffected.
  defp present_labels(def, pi) do
    grades = pi_grades(pi)
    full = def_labels(def, length(grades))

    grades
    |> Enum.zip(full)
    |> Enum.filter(fn {g, _l} -> Grade.present?(g) end)
    |> Enum.map(fn {_g, l} -> l end)
  end

  defp present_label_spans(key, pi) do
    grades = pi_grades(pi)
    spans = Cure.Elab.SourceMetadata.parameter_spans(key)
    spans = if spans == [], do: List.duplicate(nil, length(grades)), else: spans

    grades
    |> Enum.zip(spans)
    |> Enum.filter(fn {grade, _span} -> Grade.present?(grade) end)
    |> Enum.map(&elem(&1, 1))
  end

  defp pi_grades({:pi, grade, _domain, codomain}), do: [grade | pi_grades(codomain)]
  defp pi_grades(_return), do: []

  defp def_labels(def, arity) do
    case Map.get(def, :labels) do
      nil -> List.duplicate({:optional, nil}, arity)
      labels -> labels
    end
  end

  # Whether a Core term mentions any de Bruijn variable — i.e. a parameter type
  # that depends on an earlier telescope binder. Cheap structural scan over the
  # tuple/list term representation.
  defp mentions_var?({:var, _}), do: true
  defp mentions_var?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&mentions_var?/1)
  defp mentions_var?(l) when is_list(l), do: Enum.any?(l, &mentions_var?/1)
  defp mentions_var?(_leaf), do: false

  defp owners(keys), do: keys |> Enum.map(&Cure.Elab.Name.owner/1) |> Enum.uniq()
end
