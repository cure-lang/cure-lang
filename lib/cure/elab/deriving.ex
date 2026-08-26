defmodule Cure.Elab.Deriving do
  @moduledoc """
  Generate a structural typeclass instance for a `type … deriving Iface` clause.

  Deriving is defined for the canonical interfaces `Equatable` (method `eq`),
  `Ord` (method `lt`), and `Show` (method `show`). For a derivable interface this
  module synthesises an `{:implementation, …}` AST whose method matches the type's
  constructors and compares/orders each field **through that field's own instance
  method**, called by name — so a recursive field resolves to the in-progress
  instance (registered in the first pass, before any body elaborates) and a
  primitive field resolves to its primitive instance. The synthesised
  implementation is routed through `Cure.Elab.Implementation.register/2`, exactly
  like a hand-written instance, so there is no bespoke registration path.

  The generated bodies use no boolean connective and no tuple: conjunction and
  the lexicographic order fold are expressed as nested `match` on `Bool`, which is
  self-contained in any module (the retired `&&`/`||` connectives and the still-open
  flat-tuple value surface are both avoided).

  `Show` renders to `String`, but the dependent pipeline has no string
  concatenation or `Int → String` primitive yet (that arrives with the String
  value surface, roadmap #27/#29). Rather than emit a `Show` instance that cannot
  elaborate, `generate/3` returns `{:error, {:deriving_needs_strings, :Show}}`; a
  `Show` clause is added here once those primitives land.
  """

  alias Cure.Core.{Env, Inductive}
  alias Cure.Elab.Name

  @doc """
  Build the `{:implementation, …}` AST deriving `iface` for the ADT described by
  `container`. Refuses, rather than emit an instance that cannot elaborate, with:

    * `{:deriving_needs_strings, :Show}` — `Show` (no string primitives yet)
    * `{:cannot_derive, iface}` — a non-derivable interface
    * `{:no_such_interface, iface}` — the interface is not in scope
    * `{:cannot_derive_shape, iface, type}` — the container has no variants
    * `{:deriving_needs_constraints, iface, type}` — a constructor field has the
      bound type parameter's own type, so the instance would need a dictionary
      the derivation cannot thread
  """
  @spec generate(atom(), tuple(), Env.t()) :: {:ok, tuple()} | {:error, term()}
  def generate(:BeamEncode, {:container, _meta, _body} = container, env) do
    case Env.get_interface(env, :BeamEncode) do
      %{method_order: [method], methods: methods} ->
        info = Map.fetch!(methods, method)
        beam_encode_instance(container, Atom.to_string(method), info.return_type)

      nil ->
        {:error, {:no_such_interface, :BeamEncode}}

      _ ->
        {:error, {:cannot_derive, :BeamEncode}}
    end
  end

  def generate(:BeamDecode, {:container, _meta, _body} = container, env) do
    case Env.get_interface(env, :BeamDecode) do
      %{method_order: [method], methods: methods} ->
        info = Map.fetch!(methods, method)
        beam_decode_instance(container, info, env)

      nil ->
        {:error, {:no_such_interface, :BeamDecode}}

      _ ->
        {:error, {:cannot_derive, :BeamDecode}}
    end
  end

  def generate(iface, {:container, meta, body}, env)
      when iface in [:Equatable, :Ord, :Comparable, :Show, :ToJSON, :FromJSON] do
    case Env.get_interface(env, iface) do
      nil ->
        {:error, {:no_such_interface, iface}}

      desc ->
        type_name = Keyword.fetch!(meta, :name)
        type_params = Keyword.get(meta, :type_params, [])

        ctors =
          if Keyword.get(meta, :container_type) == :struct,
            do: [{type_name, length(record_fields(body))}],
            else: constructors(body)

        for_type = for_type_ast(type_name, type_params)

        with :ok <- check_derivable_shape(iface, type_name, ctors),
             :ok <- check_no_constrained_field(iface, type_name, type_params, body),
             {:ok, method_defs} <-
               method_defs(
                 iface,
                 desc,
                 type_name,
                 for_type,
                 ctors,
                 body,
                 Keyword.get(meta, :container_type) == :struct,
                 env
               ) do
          impl_meta = [interface: Atom.to_string(iface), for: type_name, for_type: for_type, as: nil]
          {:ok, {:implementation, impl_meta, method_defs}}
        end
    end
  end

  def generate(iface, _container, _env), do: {:error, {:cannot_derive, iface}}

  @doc """
  Synthesise a *structural* `Equatable` instance for a data type that has no
  hand-written one, used by the auto-derive post-pass (`Cure.Elab.Program`).

  Unlike `generate(:Equatable, …)` — which builds a per-field recursive-dispatch
  body and therefore rejects a constructor field whose type is the bound type
  parameter (`Some(t)`) — this emits a single opaque
  `Std.Builtin.struct_eq(T, a, b)` call. `struct_eq`'s type argument is
  computationally irrelevant (erased at emit), so there is no per-field
  dictionary and hence no field-shape restriction: it covers `Option(t)`,
  `Result(t, e)`, and every other generic container uniformly. The emitted spine
  is exactly what `build_binop`'s deleted `:error`-branch `struct_eq` produced, so
  ADT `==` evaluates identically to before.

  `method_name` is the `Equatable` interface's sole method name (`"=="` for the
  canonical `Std.Equatable`), taken from the in-scope interface descriptor rather
  than hardcoded, so the synthesised clause always names a real method of the
  interface it is being registered against.

  Returns `{:ok, impl_ast}` for a variant-bearing container, or `:skip` for a
  shape with no constructors (a bare record / an empty enum), which has no
  structural equality to derive.
  """
  @spec struct_eq_instance(tuple(), String.t()) :: {:ok, tuple()} | :skip
  def struct_eq_instance(container, method_name), do: struct_eq_instance(container, method_name, nil)

  @doc false
  def struct_eq_instance({:container, meta, body}, method_name, env) do
    type_name = Keyword.fetch!(meta, :name)
    type_params = Keyword.get(meta, :type_params, [])

    case constructors(body) do
      [] ->
        :skip

      ctors ->
        cond do
          # `struct_eq` receives the represented type as an explicit term-level
          # argument. If another family has a constructor with the same
          # canonical spelling (for example JSON's `Value.Number` beside the
          # `Number` type), today's Core name atom cannot disambiguate those two
          # namespaces in that term position. Decline the optional automatic
          # instance instead of generating a constructor where a type is
          # required. Authored type annotations remain unambiguous through the
          # type-position resolver.
          constructor_shadows_type_term?(env, type_name) ->
            :skip

          # The `struct_eq` type argument is spelled as `for_type` in TERM position.
          # When the type's name is also one of its constructor names (`type Iter(a) =
          # Iter(...)`, `type NonEmpty(t) = NonEmpty(t, List(t))`), that spelling
          # resolves to the constructor, not the type former, and the derived method
          # fails to elaborate (`:too_few_arguments`, or a `Pi`-vs-`Type0` mismatch when
          # the sole field is a function). No unambiguous surface spelling of the type
          # exists there, so decline to auto-derive; a hand-written `instance Equatable`
          # can still be provided.
          type_name in Enum.map(ctors, fn {name, _arity} -> name end) ->
            :skip

          # `struct_eq : Pi(a: Type0). a -> a -> Bool` accepts only `Type0` inhabitants.
          # A type with a `Type`-kinded constructor field (`type Telescope = Empty |
          # More(Type, Telescope)`) lives one universe up (`Type1`), so `struct_eq`
          # cannot be applied to it (`{:conversion_failure, {:type, 1}, {:type, 0}}`).
          Enum.any?(field_types(body), &mentions_type_universe?/1) ->
            :skip

          # An UPPER-case type parameter (`type Result(T, E) = …`) does not
          # auto-generalise: it leaks as an unbound `{:nglobal}` wherever it appears,
          # so the synthesised `for_type` (`Result(T, E)`, used both to type the
          # operands and as `struct_eq`'s erased type argument) fails to elaborate
          # with `:unknown_global`. Lower-case parameters generalise normally and
          # derive fine (`Option(t)`, `Result(t, e)`), including `==` at a concrete
          # instantiation. Rather than break elaboration of a type that merely
          # *has* an upper-case parameter (its `==` may never be used), decline to
          # auto-derive; a hand-written instance or lower-case parameters both work.
          Enum.any?(type_params, &upper_initial?/1) ->
            :skip

          true ->
            generated_type_name =
              if type_params == [], do: canonical_type_name(env, type_name), else: type_name

            for_type = for_type_ast(generated_type_name, type_params)
            impl_meta = [interface: "Equatable", for: type_name, for_type: for_type, as: nil]
            method = struct_eq_method_def(method_name, for_type, type_params, env)
            {:ok, {:implementation, impl_meta, [method]}}
        end
    end
  end

  def struct_eq_instance(_decl, _method_name, _owner), do: :skip

  defp constructor_shadows_type_term?(%Env{} = env, type_name) do
    atom = String.to_atom(type_name)
    family = Env.resolve_key(env, env.families, atom)

    case Inductive.get_ctor(env, atom) do
      nil -> false
      _ctor -> Inductive.ctor_family(env, Env.resolve_key(env, env.ctors, atom)) != family
    end
  end

  defp constructor_shadows_type_term?(_env, _type_name), do: false

  defp canonical_type_name(nil, type_name), do: type_name
  # Generated AST can carry the canonical family key directly. Using authored
  # dotted syntax here would unnecessarily re-enter module-availability lookup
  # and even makes a module's own family unavailable while its interface is
  # still being built.
  defp canonical_type_name(%Env{} = env, type_name) do
    type_name
    |> String.to_atom()
    |> then(&Env.resolve_key(env, env.families, &1))
    |> Atom.to_string()
  end

  @doc """
  Synthesise the canonical zero-copy `BeamEncode` implementation for an ADT.

  Cure constructors already erase to their native BEAM representation. The
  generated method therefore calls `Std.Beam.forget/1`, which changes only the
  static type to the opaque boundary carrier.
  """
  @spec beam_encode_instance(tuple(), String.t(), tuple()) :: {:ok, tuple()} | :skip
  def beam_encode_instance({:container, meta, body}, method_name, return_type) do
    type_name = Keyword.fetch!(meta, :name)
    type_params = Keyword.get(meta, :type_params, [])

    case constructors(body) do
      [] ->
        :skip

      _ctors ->
        if Enum.any?(type_params, &upper_initial?/1) do
          :skip
        else
          for_type = for_type_ast(type_name, type_params)
          impl_meta = [interface: "BeamEncode", for: type_name, for_type: for_type, as: nil]
          value = "beam_value"
          params = [{:param, [type: for_type], value}]

          method_meta = [
            name: method_name,
            params: params,
            return_type: return_type,
            visibility: :public,
            arity: 1
          ]

          body = {:function_call, [name: "Std.Beam.forget"], [var(value)]}
          method = {:function_def, method_meta, [body]}
          {:ok, {:implementation, impl_meta, [method]}}
        end
    end
  end

  def beam_encode_instance(_decl, _method_name, _return_type), do: :skip

  @doc "Synthesise a shape-validating `BeamDecode` implementation for a concrete ADT."
  def beam_decode_instance({:container, meta, body}, info, env) do
    type_name = Keyword.fetch!(meta, :name)
    type_params = Keyword.get(meta, :type_params, [])
    specs = constructor_specs(body)
    decoder_context = {env, type_name, derived_decoder_name(env, type_name)}

    cond do
      specs == [] ->
        :skip

      type_params != [] ->
        {:error, {:deriving_needs_constraints, :BeamDecode, String.to_atom(type_name)}}

      Enum.any?(specs, fn {_name, fields} ->
        Enum.any?(fields, &(decode_function(&1, decoder_context) == nil))
      end) ->
        {:error, {:deriving_needs_constraints, :BeamDecode, String.to_atom(type_name)}}

      true ->
        for_type = for_type_ast(type_name, [])
        impl_meta = [interface: "BeamDecode", for: type_name, for_type: for_type, as: nil]
        [{:param, pm, term_name}] = info.params
        params = [{:param, pm, term_name}]
        return_type = subst(info.return_type, "t", for_type)
        method_meta = [name: info.name, params: params, return_type: return_type, visibility: :public, arity: 1]
        method = {:function_def, method_meta, [decode_body(term_name, specs, decoder_context)]}
        {:ok, {:implementation, impl_meta, [method]}}
    end
  end

  def beam_decode_instance(_decl, _info, _env), do: :skip

  defp decode_body(term_name, specs, env) do
    tag_name = "decoded_constructor_tag"

    match(call("Std.Beam.adt_tag", [var(term_name)]), [
      arm(call("Std.Option.Some", [var(tag_name)]), decode_tag_choices(term_name, tag_name, specs, env)),
      arm(wildcard(), decode_error())
    ])
  end

  defp decode_tag_choices(_term_name, _tag_name, [], _env), do: decode_error()

  defp decode_tag_choices(term_name, tag_name, [{name, fields} | rest], env) do
    match(call("==", [var(tag_name), atom_lit(String.to_atom(name))]), [
      arm(bool(true), decode_constructor(term_name, name, fields, env)),
      arm(bool(false), decode_tag_choices(term_name, tag_name, rest, env))
    ])
  end

  defp decode_constructor(term_name, name, fields, env) do
    arity = length(fields)
    valid = decode_fields(term_name, name, fields, 0, [], env)
    actual = "decoded_constructor_arity"

    match(call("Std.Beam.adt_arity", [var(term_name)]), [
      arm(
        call("Std.Option.Some", [var(actual)]),
        match(call("==", [var(actual), int_lit(arity)]), [
          arm(bool(true), valid),
          arm(bool(false), decode_error())
        ])
      ),
      arm(wildcard(), decode_error())
    ])
  end

  defp decode_fields(_term_name, ctor, [], _index, values, _env),
    do: call("Std.Result.Ok", [call(ctor, Enum.map(Enum.reverse(values), &var/1))])

  defp decode_fields(term_name, ctor, [field_type | rest], index, values, env) do
    field_name = "decoded_field_#{index}"
    raw_name = "raw_field_#{index}"
    decoder = decode_function(field_type, env)

    decoded =
      match(call(decoder, [var(raw_name)]), [
        arm(
          call("Std.Result.Ok", [var(field_name)]),
          decode_fields(term_name, ctor, rest, index + 1, [field_name | values], env)
        ),
        arm(wildcard(), decode_error())
      ])

    match(call("Std.Beam.tuple_element", [var(term_name), int_lit(index + 1)]), [
      arm(call("Std.Option.Some", [var(raw_name)]), decoded),
      arm(wildcard(), decode_error())
    ])
  end

  defp decode_function({:variable, _meta, "Int"}, _context), do: "Std.Beam.decode_int"
  defp decode_function({:variable, _meta, "Float"}, _context), do: "Std.Beam.decode_float"
  defp decode_function({:variable, _meta, "Bool"}, _context), do: "Std.Beam.decode_bool"
  defp decode_function({:variable, _meta, "Atom"}, _context), do: "Std.Beam.decode_atom"
  defp decode_function({:variable, _meta, "String"}, _context), do: "Std.Beam.decode_string"

  defp decode_function({:variable, _meta, name}, {_env, name, self_decoder}), do: self_decoder

  defp decode_function({:variable, _meta, name}, {env, _self_name, _self_decoder}) do
    with {:ok, head} <- Cure.Elab.Resolution.resolve_bare(env, String.to_atom(name)),
         {:ok, ref} <- Cure.Elab.Coherence.lookup_anon(Env.coherence(env), :BeamDecode, head) do
      ref.methods.from_beam |> Atom.to_string()
    else
      _ -> nil
    end
  end

  defp decode_function(_, _context), do: nil

  defp derived_decoder_name(env, type_name) do
    head =
      case Cure.Elab.Resolution.resolve_bare(env, String.to_atom(type_name)) do
        {:ok, value} -> value
        _ -> String.to_atom(type_name)
      end

    base = :"__impl_BeamDecode_#{head}_from_beam"

    case Env.owner(env) do
      nil -> Atom.to_string(base)
      owner -> owner |> Cure.Elab.Name.qualify(base) |> Atom.to_string()
    end
  end

  defp decode_error(),
    do: call("Std.Result.Error", [call("Std.Beam.InvalidBeamTerm", [])])

  defp constructor_specs(body) do
    Enum.flat_map(body, fn
      {:function_def, meta, _} ->
        if Keyword.get(meta, :variant, false) do
          fields = Enum.map(Keyword.get(meta, :params, []), &constructor_field_type/1)
          [{Keyword.fetch!(meta, :name), fields}]
        else
          []
        end

      {:variable, meta, name} ->
        if Keyword.get(meta, :variant, false), do: [{name, []}], else: []

      _ ->
        []
    end)
  end

  defp constructor_field_type({:param, meta, _name}), do: Keyword.fetch!(meta, :type)
  defp constructor_field_type(type), do: type

  # The single `` `==` ``(l: T, r: T) -> Bool = Std.Builtin.struct_eq(_, l, r)`
  # method clause. `T` is the fully-applied `for_type` (`Option(t)` for a
  # parametric type), used only to type the two value parameters — a
  # type-annotation position, where a name shared by a type and its constructor
  # (`NonEmpty`, `Iter`) resolves to the type former.
  #
  # The `struct_eq` type-argument slot is a goal-directed `_`, inferred from the
  # first value operand, NOT the written `for_type`. Naming the type there would
  # re-resolve it in TERM position, where a type/constructor name clash picks the
  # constructor: `NonEmpty(t)` becomes the arity-2 constructor applied to one arg
  # (`:too_few_arguments`), and `Iter(a)` applies the `Iter` constructor — whose
  # sole field is a function type — to a type argument (`cannot_unify Pi Type0`).
  # Inferring the type from the operand sidesteps the clash entirely; the operand's
  # type is exactly `for_type`, so the erased `struct_eq` call is unchanged.
  defp struct_eq_method_def(method_name, for_type, type_params, env) do
    {left, right} = operand_names(type_params)
    params = [{:param, [type: for_type], left}, {:param, [type: for_type], right}]

    # `Bool` and `struct_eq` are spelled by the COMPILER, not by the module this
    # instance is derived into. That module never imported `Std.Bool` or
    # `Std.Builtin` and should not have to: marking the clause generated is what
    # lets the checker lower these names in checking scope rather than holding the
    # author responsible for syntax they did not write.
    meta = [
      name: method_name,
      params: params,
      return_type: ambient_bool(env),
      visibility: :public,
      arity: 2,
      compiler_generated: true
    ]

    # Same reasoning as `ambient_bool/1`: emit the canonical global key rather
    # than the qualified surface spelling. `Std.Builtin.struct_eq` as *syntax*
    # has to survive module-availability lookup in a module that never made
    # `Std.Builtin` qualified-available, and it does not — it falls through to a
    # verbatim `{:global, :"Std.Builtin.struct_eq"}` that closure validation then
    # rightly reports as unresolved. The key `Std.Builtin#struct_eq` is the
    # definition `Builtins.seed_struct_ops/2` actually registered.
    body =
      {:function_call, [name: Atom.to_string(Name.qualify("Std.Builtin", :struct_eq))],
       [for_type, var(left), var(right)]}

    {:function_def, meta, [body]}
  end

  # A pair of value-parameter names guaranteed disjoint from the type's own
  # parameter names, so neither shadows a type variable that appears in `for_type`.
  defp operand_names(type_params) do
    Enum.find(
      [{"left_value", "right_value"}, {"lhs_operand", "rhs_operand"}, {"equatable_left", "equatable_right"}],
      {"left_value", "right_value"},
      fn {l, r} -> l not in type_params and r not in type_params end
    )
  end

  # `constructors/1` recognises only `variant: true`-tagged entries, and falls through to
  # `[]` for anything else — a `rec`'s named-field list, say. With no constructors the
  # derived method's body is `match(x, [])`: a scrutinee and zero arms, unsatisfiable for
  # every input. `generate/3` is public and its contract says nothing about enum shapes, so
  # refuse here rather than emit a vacuous instance. Deriving is defined over variant types
  # in Haskell and Idris 2 alike; asking for anything else is an error at the derivation
  # site.
  defp check_derivable_shape(iface, type_name, []),
    do: {:error, {:cannot_derive_shape, iface, String.to_atom(type_name)}}

  defp check_derivable_shape(_iface, _type_name, _ctors), do: :ok

  # Deriving for a parameterized type works only while no constructor field has the bound
  # type parameter's own type. `type Box(a) = Empty | Full` and `type Tree(a) = Leaf |
  # Node(Tree(a), Tree(a))` are fine — a field of the recursive family resolves to the
  # in-progress instance. `type Lst(a) = Nil | Cons(a, Lst(a))` is not: the derived body
  # calls `eq(a0, b0)` on the `a`-typed field, `a` auto-generalizes to a RIGID type
  # variable, and the instance genuinely needs a `where Equatable(a)` dictionary the
  # derivation does not thread.
  #
  # Threading it would not be sufficient either: a concrete call `eq(l1, l2)` with
  # `l1 : Lst(Int)` must then solve `a := Int` from the argument's type to select
  # `Equatable(Int)`, and `Resolve.dict_arguments/5` matches only a parameter typed by the
  # bare head variable — it would resolve `Equatable(Lst)`, the in-progress instance
  # itself. That is a feature (dictionary passing under a type constructor), not a missing
  # keyword.
  #
  # Until it lands, refuse with a specific error rather than emit an instance whose body
  # cannot elaborate — the same discipline `generate(:Show, …)` already follows. It used to
  # emit one, and the author saw `{:no_instance, :Equatable, {:rigid, 0}}` pointing at
  # nothing they wrote. Silently resolving the wrong dictionary would be worse still.
  defp check_no_constrained_field(_iface, _type_name, [], _body), do: :ok

  defp check_no_constrained_field(iface, type_name, type_params, body) do
    if Enum.any?(field_types(body), &bare_type_param?(&1, type_params)) do
      {:error, {:deriving_needs_constraints, iface, String.to_atom(type_name)}}
    else
      :ok
    end
  end

  defp field_types(body) do
    Enum.flat_map(body, fn
      {:function_def, m, _} ->
        if Keyword.get(m, :variant, false), do: Keyword.get(m, :params, []), else: []

      {:param, meta, _name} ->
        [Keyword.fetch!(meta, :type)]

      _ ->
        []
    end)
  end

  defp bare_type_param?({:variable, _m, name}, type_params) when is_binary(name),
    do: name in type_params

  defp bare_type_param?(_ast, _type_params), do: false

  # `true` when a type-parameter name begins with an upper-case letter — the shape
  # that does not auto-generalise and leaks as a global (see the auto-derive skip).
  defp upper_initial?(<<c, _rest::binary>>) when c in ?A..?Z, do: true
  defp upper_initial?(_name), do: false

  # `true` when a constructor-field type AST references the `Type` universe anywhere
  # (`More(Type, Telescope)`, or nested as in `List(Type)`). Such a field pushes the
  # whole type into `Type1`, above the `Type0` domain of `struct_eq`.
  defp mentions_type_universe?({:variable, _m, name}) when is_binary(name),
    do: name == "Type" or String.match?(name, ~r/^Type\d+$/)

  defp mentions_type_universe?({:function_call, _m, args}) when is_list(args),
    do: Enum.any?(args, &mentions_type_universe?/1)

  defp mentions_type_universe?(_ast), do: false

  # -- constructor extraction -------------------------------------------------

  # `[{name_string, field_arity}]` in declaration order (the order that defines
  # the `Ord` constructor ranking). A field-bearing ctor is a `variant: true`
  # function_def; a nullary ctor is a `variant: true` variable.
  defp constructors(body) do
    Enum.flat_map(body, fn
      {:function_def, m, _} ->
        if Keyword.get(m, :variant, false),
          do: [{Keyword.fetch!(m, :name), length(Keyword.get(m, :params, []))}],
          else: []

      {:variable, m, name} ->
        if Keyword.get(m, :variant, false), do: [{name, 0}], else: []

      _ ->
        []
    end)
  end

  # -- method synthesis -------------------------------------------------------

  defp method_defs(iface, desc, type_name, for_type, ctors, declaration_body, record?, env) do
    Enum.reduce_while(desc.method_order, {:ok, []}, fn m, {:ok, acc} ->
      case method_def(iface, desc, m, type_name, for_type, ctors, declaration_body, record?, env) do
        {:ok, fn_def} -> {:cont, {:ok, acc ++ [fn_def]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # One mangled-nothing-yet `{:function_def, …}` for interface method `m`: its
  # signature is the interface method's signature with the head variable replaced
  # by this concrete type, its body is the structural comparator for `iface`.
  #
  # The body must scrutinise the parameters the SIGNATURE actually binds. It used to
  # hardcode `x` and `y` while the signature took its names from `info.params`, so any
  # `Equatable`/`Ord` interface not spelled with parameters literally named `x` and `y`
  # — `a1`/`a2`, `l`/`r`, `this`/`that` are all equally valid surface syntax — derived a
  # body referencing two free variables its own signature never bound. Every derived
  # instance under that interface failed to elaborate, fields or no fields. GHC's derived
  # `Eq`/`Ord` and Idris 2's `Deriving.Eq`/`Ord` cannot disagree this way: header and body
  # come from the same generation step. Now so do Cure's.
  defp method_def(iface, desc, m, type_name, for_type, ctors, declaration_body, record?, env) do
    info = Map.fetch!(desc.methods, m)

    params =
      Enum.map(info.params, fn {:param, pm, pname} ->
        {:param, Keyword.put(pm, :type, subst(Keyword.fetch!(pm, :type), desc.head_var, for_type)), pname}
      end)

    return_type = subst(info.return_type, desc.head_var, for_type)

    meta = [
      name: info.name,
      params: params,
      return_type: return_type,
      visibility: :public,
      arity: length(params)
    ]

    case Enum.map(params, fn {:param, _pm, pname} -> pname end) do
      [value] when iface == :FromJSON ->
        fields = record_fields(declaration_body)

        if not record? do
          {:error, {:cannot_derive_shape, iface, String.to_atom(type_name)}}
        else
          {:ok, {:function_def, meta, [json_decode_record_body(value, fields, type_name, info.name)]}}
        end

      [value] when iface in [:Show, :ToJSON] ->
        fields = record_fields(declaration_body)

        if not record? do
          {:error, {:cannot_derive_shape, iface, String.to_atom(type_name)}}
        else
          rendered =
            if iface == :Show,
              do: show_record_body(type_name, value, fields, info.name),
              else: json_record_body(value, fields, info.name)

          {:ok, {:function_def, meta, [rendered]}}
        end

      [left, right] ->
        record_fields = record_fields(declaration_body)

        generated_body =
          if record? do
            record_comparison_body(iface, info.name, type_name, left, right, record_fields, env)
          else
            body(iface, info.name, left, right, ctors, env)
          end

        {:ok, {:function_def, meta, [generated_body]}}

      other ->
        # `Equatable.eq` and `Ord.lt` are binary comparators. A structural body cannot be
        # synthesised for any other shape.
        {:error, {:cannot_derive_method, iface, m, {:expected_two_parameters, length(other)}}}
    end
  end

  # `Equatable.eq` — for each constructor, both sides must be that same
  # constructor and every field pair must be equal (nested-match conjunction);
  # any other pairing is `false`.
  defp body(:Equatable, eq_name, left, right, ctors, _env) do
    single = length(ctors) == 1

    arms =
      Enum.map(ctors, fn {cname, arity} ->
        inner =
          [arm(ctor_pat(cname, bs("b", arity)), eq_conj(eq_name, pairs(arity)))] ++
            if single, do: [], else: [arm(wildcard(), bool(false))]

        arm(ctor_pat(cname, bs("a", arity)), match(var(right), inner))
      end)

    match(var(left), arms)
  end

  # `Ord.lt` — `x < y` iff `x`'s constructor ranks before `y`'s; on the same
  # constructor, compare fields lexicographically (`lt` on the first differing
  # field, `eq` to advance). Cross-constructor arms fold to the constant decided
  # by declaration order.
  defp body(:Ord, lt_name, left, right, ctors, env) do
    eq_name = equatable_method(env)
    indexed = Enum.with_index(ctors)

    arms =
      Enum.map(indexed, fn {{cname, arity}, i} ->
        inner =
          Enum.map(indexed, fn {{cname2, arity2}, j} ->
            cond do
              j > i -> arm(ctor_pat(cname2, ignore(arity2)), bool(true))
              j < i -> arm(ctor_pat(cname2, ignore(arity2)), bool(false))
              true -> arm(ctor_pat(cname2, bs("r", arity2)), lt_lex(lt_name, eq_name, lex_pairs(arity)))
            end
          end)

        arm(ctor_pat(cname, bs("l", arity)), match(var(right), inner))
      end)

    match(var(left), arms)
  end

  defp body(:Comparable, lt_name, left, right, ctors, env),
    do: body(:Ord, lt_name, left, right, ctors, env)

  defp record_comparison_body(iface, method, type_name, left, right, fields, env) do
    body(iface, method, left, right, [{type_name, length(fields)}], env)
  end

  defp show_record_body(type_name, value, fields, method) do
    contents =
      fields
      |> Enum.with_index()
      |> Enum.flat_map(fn {{field, _type}, index} ->
        separator = if index == 0, do: "", else: ", "

        [
          string(separator <> field <> ": "),
          call(method, [field_access(value, field)])
        ]
      end)

    concat([string(type_name <> "{")] ++ contents ++ [string("}")])
  end

  defp json_record_body(value, fields, method) do
    members =
      Enum.map(fields, fn {field, _type} ->
        call("member", [string(field), call(method, [field_access(value, field)])])
      end)

    call("Object", [{:list, [], members}])
  end

  defp json_decode_record_body(value, fields, type_name, method) do
    members = "__json_members"

    match(var(value), [
      arm(ctor_pat("Object", [members]), json_decode_fields(fields, members, type_name, method, [], 0)),
      arm(
        wildcard(),
        call("Error", [call("UnexpectedValue", [string("expected JSON object for #{type_name}")])])
      )
    ])
  end

  defp json_decode_fields([], _members, type_name, _method, decoded, _index) do
    fields =
      Enum.map(Enum.reverse(decoded), fn {field, binder} ->
        {:pair, [], [atom_lit(String.to_atom(field)), var(binder)]}
      end)

    call("Ok", [{:function_call, [name: type_name, record: true], fields}])
  end

  defp json_decode_fields([{field, field_type} | rest], members, type_name, method, decoded, index) do
    raw = "__json_raw_#{index}"
    result = "__json_value_#{index}"
    reason = "__json_error_#{index}"
    result_type = call("Result", [field_type, var("DecodeError")])
    decode = {:assert_type, [], [call(method, [var(raw)]), result_type]}

    decoded_field =
      match(decode, [
        arm(
          ctor_pat("Ok", [result]),
          json_decode_fields(rest, members, type_name, method, [{field, result} | decoded], index + 1)
        ),
        arm(ctor_pat("Error", [reason]), call("Error", [var(reason)]))
      ])

    match(call("required_member", [string(field), var(members)]), [
      arm(ctor_pat("Ok", [raw]), decoded_field),
      arm(ctor_pat("Error", [reason]), call("Error", [var(reason)]))
    ])
  end

  defp record_fields(body) do
    Enum.flat_map(body, fn
      {:param, meta, name} -> [{name, Keyword.fetch!(meta, :type)}]
      _ -> []
    end)
  end

  defp field_access(value, field),
    do: {:attribute_access, [attribute: field], [var(value)]}

  defp string(value), do: {:literal, [subtype: :string], value}
  defp concat([single]), do: single

  defp concat([head | tail]),
    do: {:binary_op, [category: :concatenation, operator: :<>], [head, concat(tail)]}

  # The equality method name to call from a derived `Ord` (its lexicographic
  # fold advances on equal fields). Read from the in-scope `Equatable` interface;
  # defaults to the canonical `"eq"` if none is registered.
  defp equatable_method(env) do
    case Env.get_interface(env, :Equatable) do
      %{method_order: [m | _], methods: methods} -> Map.fetch!(methods, m).name
      _ -> "eq"
    end
  end

  # Right-folded conjunction of `eq(l_i, r_i)` as nested `Bool` matches.
  defp eq_conj(_eq, []), do: bool(true)
  defp eq_conj(eq, [{l, r}]), do: call(eq, [var(l), var(r)])

  defp eq_conj(eq, [{l, r} | rest]) do
    match(call(eq, [var(l), var(r)]), [
      arm(bool(true), eq_conj(eq, rest)),
      arm(bool(false), bool(false))
    ])
  end

  # Lexicographic `<` over same-constructor fields: `lt` on the first field; if
  # equal, recurse; the empty (all-equal) tail is `false` (not strictly less).
  defp lt_lex(_lt, _eq, []), do: bool(false)
  defp lt_lex(lt, _eq, [{l, r}]), do: call(lt, [var(l), var(r)])

  defp lt_lex(lt, eq, [{l, r} | rest]) do
    match(call(lt, [var(l), var(r)]), [
      arm(bool(true), bool(true)),
      arm(
        bool(false),
        match(call(eq, [var(l), var(r)]), [
          arm(bool(true), lt_lex(lt, eq, rest)),
          arm(bool(false), bool(false))
        ])
      )
    ])
  end

  # -- field-name plumbing ----------------------------------------------------

  # `["<p>0", "<p>1", …]` — fresh binder names for a constructor's fields.
  defp bs(prefix, arity), do: for(i <- 0..(arity - 1)//1, do: "#{prefix}#{i}")

  # `arity` wildcards, for a constructor whose fields the arm ignores.
  defp ignore(arity), do: List.duplicate("_", arity)

  # Field-binder pairs `{"a_i", "b_i"}` for `Equatable`'s two matched scrutinees.
  defp pairs(arity), do: for(i <- 0..(arity - 1)//1, do: {"a#{i}", "b#{i}"})

  # Field-binder pairs `{"l_i", "r_i"}` for `Ord`'s two matched scrutinees.
  defp lex_pairs(arity), do: for(i <- 0..(arity - 1)//1, do: {"l#{i}", "r#{i}"})

  # -- AST constructors -------------------------------------------------------

  defp var(name), do: {:variable, [scope: :local], name}

  # The ambient `Std.Bool.Bool` as a qualified type reference, NOT bare `Bool`.
  # `struct_eq`'s result is fixed to `Std.Bool#Bool`, so an auto-derived `==`
  # must declare that exact return type. A bare `Bool` re-resolves in the host
  # module's scope, and a module that shadows the prelude (`type Bool = T | F`)
  # would bind it to the LOCAL type — the derived body then fails conversion
  # (`struct_eq : … -> Std.Bool#Bool` vs declared local `Bool`). The qualified
  # spelling routes through `Resolution.resolve_qualified/3`, which is immune to
  # local shadowing and lands on the canonical family in every module.
  # Preferred spelling: the canonical family key itself, which is what
  # `Inductive.builtin(env, :bool)` records. Generated AST may carry a canonical
  # key directly (same reasoning as `canonical_type_name/2`), and doing so keeps
  # the derived signature out of module-availability lookup entirely — the host
  # module never imported `Std.Bool` and need not, since it did not write this.
  defp ambient_bool(%Env{} = env) do
    case Inductive.builtin(env, :bool) do
      nil -> ambient_bool(nil)
      key -> var(Atom.to_string(key))
    end
  end

  defp ambient_bool(_env),
    do:
      {:attribute_access, [attribute: "Bool"],
       [{:attribute_access, [attribute: "Bool"], [{:variable, [scope: :local], "Std"}]}]}

  defp wildcard(), do: {:variable, [scope: :local], "_"}
  defp bool(b), do: {:literal, [subtype: :boolean], b}
  defp int_lit(value), do: {:literal, [subtype: :integer], value}
  defp atom_lit(value), do: {:literal, [subtype: :symbol], value}
  defp call(name, args), do: {:function_call, [name: name], args}
  defp match(scrut, arms), do: {:pattern_match, [], [scrut | arms]}
  defp arm(pattern, body), do: {:match_arm, [pattern: pattern], [body]}

  # A constructor pattern is always a `{:function_call, …}` — even nullary, whose
  # empty arg list distinguishes it from a bare-variable *catch-all* arm (which
  # `partition_arms` would treat as a default that swallows every constructor).
  defp ctor_pat(name, binders), do: {:function_call, [name: name], Enum.map(binders, &var/1)}

  # -- head substitution ------------------------------------------------------

  defp subst({:variable, _m, name}, head_var, for_type) when name == head_var, do: for_type
  defp subst({:variable, _m, _} = v, _head_var, _for_type), do: v

  defp subst({:function_call, m, args}, head_var, for_type),
    do: {:function_call, m, Enum.map(args, &subst(&1, head_var, for_type))}

  defp subst(other, _head_var, _for_type), do: other

  # -- for-type AST -----------------------------------------------------------

  defp for_type_ast(type_name, []), do: var(type_name)

  defp for_type_ast(type_name, params),
    do: {:function_call, [name: type_name], Enum.map(params, &var/1)}
end
