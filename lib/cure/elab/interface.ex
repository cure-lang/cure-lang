defmodule Cure.Elab.Interface do
  @moduledoc """
  Elaborate a compile-time `interface` (typeclass) declaration.

  An interface `interface Eqs(a)` with methods `eqs : a -> a -> Bool` is the
  successor to the runtime `proto`. Conceptually it denotes a dependent record
  type former `Eqs : Π(h : K). Type` — `Eqs(h) ≙ record{ eqs : h -> h -> Bool }`
  — whose head kind `K` is inferred from how the head variable is used across the
  method signatures (`:type` when it appears bare, `{:arrow, :type, :type}` when
  it appears applied, e.g. `Functor`'s `f(a)`).

  This module registers the *descriptor* (elaborator-level metadata: head var,
  head kind, per-method surface signatures, default bodies) in the env under the
  interface's name atom. The Core record type former and the dictionary values
  that inhabit it are built by `Cure.Elab.Implementation` (Task 3) and consumed by
  `Cure.Elab.Resolve` (Tasks 4/5) — an interface with no implementations needs no
  Core type, so building the former lazily keeps a bare `interface` cheap and
  side-steps method-level generics until an instance actually forces the issue.
  """

  alias Cure.Core.Env
  alias Cure.MetaAST.Metadata

  @doc """
  Register the interface descriptor for `{:interface, meta, methods}` in `env`.
  Returns `{:error, {:inconsistent_head_kind, name}}` if the head variable is
  used both bare and applied across the method signatures.
  """
  @spec elaborate(tuple(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate({:interface, meta, methods}, env) do
    name = Keyword.fetch!(meta, :name)
    name_atom = String.to_atom(name)
    head_var = meta |> Keyword.get(:params, []) |> List.first()
    defaults = Keyword.get(meta, :defaults, %{})
    # Superinterface names from the `requires` clause, normalized to atoms. An
    # interface with no `requires` clause gets `super: []`, so the obligation
    # check at instance registration is a no-op for it.
    super_interfaces =
      meta |> Keyword.get(:requires, []) |> Enum.map(&String.to_atom/1)

    with :ok <- reject_reserved_family_name(name_atom),
         {:ok, head_kind} <- infer_head_kind(name_atom, head_var, methods, meta) do
      desc =
        Metadata.strip_diagnostics(%{
          name: name_atom,
          owner: Env.owner(env),
          head_var: head_var,
          head_kind: head_kind,
          methods: build_method_map(methods),
          method_order: method_order(methods),
          defaults: defaults,
          super: super_interfaces
        })

      with :ok <- check_method_names_free(desc, env, methods),
           {:ok, env1} <- declare_dictionary_former(desc, env) do
        register_method_spans(desc.name, methods)
        {:ok, Env.put_interface(env1, name_atom, desc)}
      end
    end
  end

  # An `interface` declares a type name like any `type` or `typealias` does, so
  # the generated-family namespace (`Union<…>` / `Disjoint<…>`, reachable through
  # backtick-quoted identifiers) has to be reserved against it too — the same
  # guard `Cure.Elab.Declarations` applies to every other type-name declaration.
  #
  # It runs FIRST, before head-kind inference and before method registration.
  # A reserved name is not a declaration at all, so nothing about its members
  # should be diagnosed: registering them first meant a reserved interface whose
  # method collided with an ambient one (`combine`, from the `@prelude`
  # `Std.Semigroup`) reported the collision and never reached this check.
  defp reject_reserved_family_name(name) do
    if Cure.Elab.Union.reserved_name?(name),
      do: {:error, {:reserved_union_type_name, name}},
      else: :ok
  end

  # `for_method/2` is the SOLE lookup `Resolve.method_call` uses to find the interface owning an
  # unqualified call like `size(x)`, and it is `Enum.find_value/2` over the whole `env.interfaces`
  # map — the FIRST interface, in unspecified map-iteration order, whose method table holds the
  # name. Nothing anywhere checked whether a method name is unique across in-scope interfaces, so
  # two interfaces both declaring `size` left every unqualified call bound to whichever descriptor
  # the map happened to yield first, with no diagnostic at the declaration or the call.
  #
  # Idris2 and Lean 4 both require disambiguation when two in-scope interfaces/classes declare a
  # same-named method: an unqualified reference that cannot be disambiguated is a compile error,
  # never an arbitrary pick. Cure has no qualified method-call syntax, so the ambiguity can only
  # be reported where it is created.
  defp check_method_names_free(desc, %Env{interfaces: ifaces}, methods) do
    desc.method_order
    |> Enum.find_value(fn m ->
      Enum.find_value(ifaces, fn {other, other_desc} ->
        if other != desc.name and Map.has_key?(other_desc.methods, m), do: {m, other}
      end)
    end)
    |> case do
      nil ->
        :ok

      {method, other} ->
        interfaces = Enum.sort([desc.name, other])
        current_span = method_span(methods, method)
        other_span = Cure.Elab.SourceMetadata.interface_method_span(other, method)

        {:error,
         {:source_context, {:ambiguous_method, method, interfaces},
          %{
            span: current_span,
            method: method,
            interfaces: interfaces,
            method_declarations: [
              %{interface: other, span: other_span},
              %{interface: desc.name, span: current_span}
            ],
            checking: desc.name,
            expectation_origin: :interface_declaration,
            expression_category: :interface_method
          }}}
    end
  end

  defp register_method_spans(interface, methods) do
    Enum.each(methods, fn
      {:function_def, meta, _body} ->
        method = meta |> Keyword.fetch!(:name) |> String.to_atom()
        :ok = Cure.Elab.SourceMetadata.put_interface_method_span(interface, method, method_span(meta))

      _other ->
        :ok
    end)
  end

  defp method_span(methods, method) when is_list(methods) do
    Enum.find_value(methods, fn
      {:function_def, meta, _body} ->
        if String.to_atom(Keyword.fetch!(meta, :name)) == method, do: method_span(meta)

      _other ->
        nil
    end)
  end

  defp method_span(meta) when is_list(meta) do
    case Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{name: span} when not is_nil(span) -> span
      %Cure.MetaAST.SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  # The interface's dictionary type former: a single-constructor record family
  # `Iface(head) ≙ Iface{ method : field-type, … }`. For a kind-`Type` interface
  # this is a plain parameterized record; the higher-kinded former (a `f : Type ->
  # Type` parameter) is built by the HKT resolution step and skipped here.
  defp declare_dictionary_former(%{head_kind: :type} = desc, env) do
    fields =
      Enum.map(desc.method_order, fn m ->
        info = Map.fetch!(desc.methods, m)
        {:param, [type: info.type_ast], info.name}
      end)

    Cure.Elab.Declarations.declare_record(desc.name, [desc.head_var], fields, env)
  end

  defp declare_dictionary_former(_desc, env), do: {:ok, env}

  @doc "The interface descriptor whose method set contains `method`, or nil."
  @spec for_method(Env.t(), atom()) :: map() | nil
  def for_method(%Env{interface_methods: methods}, method), do: Map.get(methods, method)

  @doc false
  @spec merge_tables(map(), map()) :: {:ok, map()} | {:error, term()}
  def merge_tables(left, right) when is_map(left) and is_map(right) do
    interfaces = Map.merge(left, right)

    interfaces
    |> method_owners()
    |> Enum.find(fn {_method, owners} -> length(owners) > 1 end)
    |> case do
      nil ->
        {:ok, interfaces}

      {method, owners} ->
        owners = Enum.sort(owners)
        primary = List.last(owners)
        primary_span = Cure.Elab.SourceMetadata.interface_method_span(primary, method)

        {:error,
         {:source_context, {:ambiguous_method, method, owners},
          %{
            span: primary_span,
            method: method,
            interfaces: owners,
            method_declarations:
              Enum.map(owners, fn interface ->
                %{
                  interface: interface,
                  span: Cure.Elab.SourceMetadata.interface_method_span(interface, method)
                }
              end),
            checking: primary,
            expectation_origin: :interface_merge,
            expression_category: :interface_method
          }}}
    end
  end

  defp method_owners(interfaces) do
    interfaces
    |> Enum.reduce(%{}, fn {interface, descriptor}, owners ->
      Enum.reduce(Map.keys(descriptor.methods), owners, fn method, owners ->
        Map.update(owners, method, [interface], &[interface | &1])
      end)
    end)
    |> Enum.map(fn {method, owners} -> {method, Enum.uniq(owners)} end)
    |> Enum.sort_by(&elem(&1, 0))
  end

  # -- descriptor construction ------------------------------------------------

  # method_map: %{method_atom => %{name, params, return_type, type_ast}} where
  # `type_ast` is the synthesized surface function-type `T1 -> ... -> Tn -> R`
  # (the interface record's field type for this method).
  defp build_method_map(methods) do
    methods
    |> Enum.flat_map(fn
      {:function_def, m, _body} ->
        mname = Keyword.fetch!(m, :name)
        params = Keyword.get(m, :params, [])
        return_type = Keyword.get(m, :return_type)

        [
          {String.to_atom(mname),
           %{
             name: mname,
             params: params,
             return_type: return_type,
             type_ast: method_type_ast(params, return_type)
           }}
        ]

      _ ->
        []
    end)
    |> Map.new()
  end

  defp method_order(methods) do
    methods
    |> Enum.flat_map(fn
      {:function_def, m, _body} -> [String.to_atom(Keyword.fetch!(m, :name))]
      _ -> []
    end)
  end

  # Fold a method's parameter types + return type into a surface function-type
  # AST `T1 -> ... -> Tn -> R`, the shape `idx_to_core` lowers to a Pi chain
  # (`{:function_call, [function_type: true], [doms..., result]}`).
  defp method_type_ast(params, return_type) do
    dom_asts = Enum.map(params, fn {:param, pm, _pname} -> Keyword.fetch!(pm, :type) end)
    {:function_call, [function_type: true], dom_asts ++ [return_type]}
  end

  # -- head-kind inference ----------------------------------------------------

  # Scan every method signature (param types + return type) for uses of the head
  # variable. A bare occurrence (`a`) contributes `:type`; an applied occurrence
  # (`a(...)`, i.e. `f(x)`) contributes `:arrow`. Both present ⇒ inconsistent.
  defp infer_head_kind(_name, nil, _methods, _meta), do: {:ok, :type}

  defp infer_head_kind(name, head_var, methods, interface_meta) do
    uses =
      methods
      |> Enum.flat_map(&method_type_asts/1)
      |> Enum.reduce(MapSet.new(), fn ast, acc -> collect_head_uses(ast, head_var, acc) end)

    cond do
      MapSet.member?(uses, :bare) and MapSet.member?(uses, :applied) ->
        sites = head_use_sites(methods, head_var)
        primary = Enum.find(sites, &(&1.kind == :applied)) || List.first(sites)
        interface_info = Metadata.source_info(interface_meta)

        {:error,
         {:source_context, {:inconsistent_head_kind, name},
          %{
            span: primary && primary.span,
            interface: name,
            head_parameter: head_var,
            head_uses: sites,
            declaration_span: interface_info && interface_info.whole,
            declaration_name_span: interface_info && interface_info.name,
            checking: name,
            expectation_origin: :interface_head_kind,
            expression_category: :interface_type
          }}}

      MapSet.member?(uses, :applied) ->
        {:ok, {:arrow, :type, :type}}

      true ->
        {:ok, :type}
    end
  end

  defp method_type_asts({:function_def, m, _body}) do
    param_types = m |> Keyword.get(:params, []) |> Enum.map(fn {:param, pm, _} -> Keyword.fetch!(pm, :type) end)

    case Keyword.get(m, :return_type) do
      nil -> param_types
      rt -> param_types ++ [rt]
    end
  end

  defp method_type_asts(_), do: []

  # Walk a type AST accumulating {:bare, :applied} head-var uses.
  defp collect_head_uses({:variable, _meta, name}, head_var, acc) do
    if name == head_var, do: MapSet.put(acc, :bare), else: acc
  end

  defp collect_head_uses({:function_call, fmeta, args}, head_var, acc) do
    acc =
      cond do
        Keyword.get(fmeta, :function_type) -> acc
        Keyword.get(fmeta, :name) == head_var -> MapSet.put(acc, :applied)
        true -> acc
      end

    Enum.reduce(args, acc, fn a, inner -> collect_head_uses(a, head_var, inner) end)
  end

  defp collect_head_uses(_other, _head_var, acc), do: acc

  defp head_use_sites(methods, head_var) do
    Enum.flat_map(methods, fn
      {:function_def, meta, _body} ->
        method = Keyword.get(meta, :name)

        meta
        |> Keyword.get(:params, [])
        |> Enum.map(fn {:param, parameter_meta, _name} -> Keyword.get(parameter_meta, :type) end)
        |> then(fn types -> List.wrap(Keyword.get(meta, :return_type)) ++ types end)
        |> Enum.flat_map(&collect_head_use_sites(&1, head_var, method))

      _other ->
        []
    end)
  end

  defp collect_head_use_sites({:variable, meta, name}, head_var, method) do
    if name == head_var,
      do: [%{kind: :bare, method: method, span: ast_role_span(meta, :name)}],
      else: []
  end

  defp collect_head_use_sites({:function_call, meta, arguments}, head_var, method) do
    own =
      if Keyword.get(meta, :function_type) != true and Keyword.get(meta, :name) == head_var do
        [%{kind: :applied, method: method, span: ast_role_span(meta, :callee)}]
      else
        []
      end

    own ++ Enum.flat_map(arguments, &collect_head_use_sites(&1, head_var, method))
  end

  defp collect_head_use_sites({_tag, _meta, children}, head_var, method) when is_list(children),
    do: Enum.flat_map(children, &collect_head_use_sites(&1, head_var, method))

  defp collect_head_use_sites(list, head_var, method) when is_list(list),
    do: Enum.flat_map(list, &collect_head_use_sites(&1, head_var, method))

  defp collect_head_use_sites(_other, _head_var, _method), do: []

  defp ast_role_span(meta, role) do
    case Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{} = info -> Map.get(info, role) || info.name || info.whole
      _ -> nil
    end
  end
end
