defmodule Cure.Diagnostic.Adapter.KernelTest do
  use ExUnit.Case, async: true

  alias Cure.Diagnostic.{Adapter, Renderer, SourceRegistry}
  alias Cure.Diagnostic.Adapter.Kernel, as: KernelAdapter

  test "strict positivity points at the negative occurrence and its constructor" do
    source = "MkBad Bad\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:positivity, source, "positivity.cure")
    {:ok, constructor_span} = SourceRegistry.span(registry, :positivity, 0, 5)
    {:ok, occurrence_span} = SourceRegistry.span(registry, :positivity, 6, 9)

    error =
      {:source_context, {:non_strictly_positive, :"Demo#MkBad"},
       %{
         span: occurrence_span,
         constructor_span: constructor_span,
         family_name: "Bad",
         precise_occurrence: true
       }}

    direct = KernelAdapter.from_error(error)
    assert Adapter.from_error(error) == direct

    assert Renderer.plain(direct, registry, width: 80) ==
             """
             -- RECURSIVE TYPE APPEARS IN A FUNCTION INPUT [E103] ----------- positivity.cure

             `Bad` appears in a function input stored by `MkBad`. A recursive type may appear
             in a stored function's result, but not in one of its inputs.

             at positivity.cure:1:7
             1 | MkBad Bad
               | ----- ^^^ this constructor stores the unsafe function type; recursive `Bad` is consumed here

             Hint: Move `Bad` to the function result, or make the input non-recursive
             """
             |> String.trim_trailing()
  end

  test "a rejected constructor field names the type it had to be and why it was not" do
    # "A dependent index does not agree with the value required by this expression"
    # is true of every rejection this branch produces and actionable for none of
    # them. The kernel knows which family the field had to be and what went wrong;
    # both belong in the message.
    source = "Wrap(chars)\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:field, source, "field.cure")
    {:ok, span} = SourceRegistry.span(registry, :field, 5, 10)

    error = {:index_mismatch, {:in_field_of, :"Std.String#String", {:foreign_ctor, :"Std.List#Cons"}}}

    assert Renderer.plain(KernelAdapter.from_error(error, span: span), registry, width: 80) ==
             """
             -- CONSTRUCTOR ARGUMENT IS NOT A `STRING` [E093] -------------------- field.cure

             This constructor argument must be a `String`, but `Cons` is a constructor of a
             different type.

             at field.cure:1:6
             1 | Wrap(chars)
               |      ^^^^^ this is not a `String`

             Hint: Build this argument with a constructor of `String`, or convert the value first
             """
             |> String.trim_trailing()
  end

  test "a genuine index disagreement still reads as one" do
    # The remaining shape: both sides ARE the family, their indices differ. The
    # category is unchanged -- only the discarded cause is new.
    error = {:index_mismatch, {:in_field_of, :SF, {:cannot_unify, :actual, :expected}}}
    diagnostic = KernelAdapter.from_error(error)

    assert diagnostic.title == "Dependent index mismatch"
    assert Adapter.from_error(error) == diagnostic
  end

  test "the kernel family rejects non-kernel variants" do
    assert_raise Cure.Diagnostic.UnhandledError, fn ->
      KernelAdapter.from_error({:unknown_global, :missing})
    end
  end

  test "trusted type rejections are owned by the kernel adapter" do
    source = "bad\n"
    registry = SourceRegistry.new() |> SourceRegistry.register(:kernel, source, "kernel.cure")
    {:ok, span} = SourceRegistry.span(registry, :kernel, 0, 3)

    errors = [
      {:index_mismatch, :details},
      {:cannot_unify, :actual, :expected},
      {:escaping_variable, 1},
      {:occurs_check, 1, :term},
      {:ctor_requires_checking_mode, :Family},
      {:bounded_bound_not_concrete, :bound},
      :arg_arity,
      :ctor_arity,
      :domain_mismatch,
      :grade_mismatch,
      :bad_motive,
      :not_a_type,
      :not_a_type_value,
      :universe_level,
      :universe_ceiling
    ]

    for error <- errors do
      direct = KernelAdapter.from_error(error, span: span)
      assert Adapter.from_error(error, span: span) == direct
      assert direct.code == "E093"
      assert direct.primary.span == span
      assert direct.payload.kind
    end

    rendered =
      KernelAdapter.from_error({:cannot_unify, :actual, :expected},
        span: span
      )
      |> Renderer.plain(registry, width: 80)

    assert rendered =~ "TYPES CANNOT BE UNIFIED [E093]"
    assert rendered =~ "^^^ change the expression or annotation so the types agree"
  end
end
