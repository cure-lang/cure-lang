defmodule Cure.Diagnostic.Adapter.Kernel do
  @moduledoc "Converts trusted-kernel rejection values into authored diagnostics."

  alias Cure.Diagnostic
  alias Cure.Diagnostic.{Doc, Label, Span, Suggestion}

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:non_strictly_positive, constructor}, opts),
    do: positivity_failure(constructor, %{}, opts)

  def from_error({:source_context, {:non_strictly_positive, constructor}, context}, opts)
      when is_map(context) do
    opts =
      case Map.get(context, :span) do
        %Span{} = span -> Keyword.put_new(opts, :span, span)
        _ -> opts
      end

    positivity_failure(constructor, context, opts)
  end

  def from_error({:index_mismatch, {:in_field_of, family, cause}}, opts),
    do: rejected_field(family, cause, opts)

  def from_error({:index_mismatch, _details}, opts),
    do: type_failure(:index_mismatch, opts)

  def from_error({:cannot_unify, _actual, _expected}, opts),
    do: type_failure(:cannot_unify, opts)

  def from_error({:escaping_variable, _id}, opts),
    do: type_failure(:escaping_variable, opts)

  def from_error({:ctor_requires_checking_mode, _family}, opts),
    do: type_failure(:ctor_requires_checking_mode, opts)

  def from_error({:bounded_bound_not_concrete, _bound}, opts),
    do: type_failure(:bounded_bound_not_concrete, opts)

  def from_error({:occurs_check, _id, _term}, opts),
    do: type_failure(:occurs_check, opts)

  def from_error(kind, opts)
      when kind in [
             :arg_arity,
             :ctor_arity,
             :domain_mismatch,
             :grade_mismatch,
             :bad_motive,
             :not_a_type,
             :not_a_type_value,
             :index_mismatch,
             :universe_level,
             :universe_ceiling,
             :hole_in_inference_position,
             :ctor_requires_checking_mode,
             :bounded_bound_not_concrete
           ],
      do: type_failure(kind, opts)

  def from_error(error, _opts), do: raise(Cure.Diagnostic.UnhandledError, error: error)

  defp positivity_failure(constructor, context, opts) do
    family = Map.get(context, :family_name)
    precise? = Map.get(context, :precise_occurrence, false)
    constructor_name = surface_name(constructor)

    {title, body, primary_message, hint} =
      if precise? and is_binary(family) do
        {
          "Recursive type appears in a function input",
          "`#{family}` appears in a function input stored by `#{constructor_name}`. A recursive type may appear in a stored function's result, but not in one of its inputs.",
          "recursive `#{family}` is consumed here",
          "Move `#{family}` to the function result, or make the input non-recursive"
        }
      else
        {
          "Non-strictly-positive type",
          "The recursive occurrence in `#{constructor_name}` cannot be proven strictly positive, so this type cannot be accepted by the normalising kernel.",
          "this constructor is not strictly positive",
          "Move recursive types out of function-input and other negative positions in this constructor"
        }
      end

    secondary =
      if precise? do
        case label(Map.get(context, :constructor_span), :secondary, "this constructor stores the unsafe function type") do
          nil -> []
          label -> [label]
        end
      else
        []
      end

    Diagnostic.new(
      code: "E103",
      key: :non_strictly_positive_type,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary(opts, primary_message),
      secondary: secondary,
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: %{family: family, constructor: constructor, precise_occurrence: precise?}
    )
  end

  # A constructor argument the kernel refused against the family it was declared
  # at. `field_cause/2` turns the underlying rejection into the sentence that
  # explains it; when the cause is two indices of the SAME family disagreeing,
  # there is nothing to add and this stays the plain index-mismatch report.
  defp rejected_field(family, cause, opts) do
    name = surface_name(family)

    case field_cause(cause, name) do
      nil ->
        type_failure(:index_mismatch, opts)

      {explanation, hint} ->
        Diagnostic.new(
          code: "E093",
          key: :type_mismatch,
          severity: :error,
          title: "Constructor argument is not a `#{name}`",
          body: Doc.paragraph("This constructor argument must be a `#{name}`, but #{explanation}."),
          primary: primary(opts, "this is not a `#{name}`"),
          suggestions: [%Suggestion{message: hint, applicability: :manual}],
          payload: %{kind: :index_mismatch, family: family, cause: cause}
        )
    end
  end

  defp field_cause({:foreign_ctor, constructor}, family),
    do:
      {"`#{surface_name(constructor)}` is a constructor of a different type",
       "Build this argument with a constructor of `#{family}`, or convert the value first"}

  defp field_cause({:unknown_ctor, constructor}, family),
    do:
      {"`#{surface_name(constructor)}` is not a constructor of `#{family}`",
       "Use one of `#{family}`'s own constructors"}

  defp field_cause({:unknown_global, name, _context}, _family),
    do:
      {"`#{surface_name(name)}` is not defined here", "Define `#{surface_name(name)}`, or import the module that does"}

  defp field_cause({:unknown_global, name}, _family),
    do:
      {"`#{surface_name(name)}` is not defined here", "Define `#{surface_name(name)}`, or import the module that does"}

  defp field_cause(:ctor_arity, family),
    do:
      {"the constructor here was given a different number of arguments than it declares",
       "Supply exactly the arguments `#{family}`'s constructor declares"}

  # `:cannot_unify` and `:conversion_failure` between two values of the family are
  # exactly what "index mismatch" already says, so they keep the existing report.
  defp field_cause(_cause, _family), do: nil

  defp type_failure(kind, opts) do
    {title, body, message} =
      case kind do
        :index_mismatch ->
          {"Dependent index mismatch", "A dependent index does not agree with the value required by this expression.",
           "make the indexed values agree"}

        :cannot_unify ->
          {"Types cannot be unified", "The type checker could not make these types definitionally equal.",
           "change the expression or annotation so the types agree"}

        :escaping_variable ->
          {"Type variable escapes its scope", "A type variable would escape the scope in which it was introduced.",
           "keep this type variable within its binding"}

        :occurs_check ->
          {"Infinite type detected", "A type variable would have to contain itself, producing an infinite type.",
           "break the recursive type equation"}

        :arg_arity ->
          {"Wrong number of type arguments",
           "This type application has a different number of arguments than its declaration.",
           "supply exactly the declared arguments"}

        :ctor_arity ->
          {"Wrong number of constructor arguments",
           "This constructor application has a different number of arguments than its declaration.",
           "supply exactly the constructor arguments"}

        :domain_mismatch ->
          {"Function domain mismatch", "This function is being applied to a value of the wrong type.",
           "change the argument to match the function domain"}

        :grade_mismatch ->
          {"Relevance grade mismatch", "This value is used with a relevance grade that its type does not allow.",
           "use the value at its declared relevance"}

        :bad_motive ->
          {"Invalid case motive", "The dependent case motive is not a well-formed type family.",
           "make the case motive a function over the scrutinee"}

        :not_a_type ->
          {"Expected a type", "This expression does not evaluate to a type where one is required.",
           "use a type expression here"}

        :not_a_type_value ->
          {"Expected a type value", "This expression is not a valid type value in this position.",
           "use a well-formed type value"}

        :universe_level ->
          {"Universe level mismatch", "This type lives above the universe level allowed here.",
           "lower the universe level or widen the surrounding type"}

        :universe_ceiling ->
          {"Universe level is too high", "This type would exceed Cure's supported universe ceiling.",
           "reduce the universe level"}

        :hole_in_inference_position ->
          {"Hole needs an expected type", "This hole appears where the kernel cannot infer its type.",
           "add an annotation that determines the hole's type"}

        :ctor_requires_checking_mode ->
          {"Constructor needs an expected type", "This constructor cannot be inferred without checking information.",
           "add a type annotation at the constructor use"}

        :bounded_bound_not_concrete ->
          {"Bound must be concrete", "This bounded type declaration requires a concrete bound.",
           "replace the bound with a concrete value"}
      end

    Diagnostic.new(
      code: "E093",
      key: :type_mismatch,
      severity: :error,
      title: title,
      body: Doc.paragraph(body),
      primary: primary(opts, message),
      payload: %{kind: kind}
    )
  end

  defp primary(opts, message) do
    case Keyword.get(opts, :span) do
      %Span{} = span -> %Label{span: span, style: :primary, message: Keyword.get(opts, :label, message)}
      _ -> nil
    end
  end

  defp label(%Span{} = span, style, message), do: %Label{span: span, style: style, message: message}
  defp label(_, _style, _message), do: nil

  defp surface_name(name) do
    name
    |> name_to_string()
    |> String.split("#")
    |> List.last()
  end

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)
end
