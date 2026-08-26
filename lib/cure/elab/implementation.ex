defmodule Cure.Elab.Implementation do
  @moduledoc """
  Elaborate a compile-time `implementation` (typeclass instance).

  Each method of the instance is lowered to an ordinary global definition with a
  mangled, collision-proof name (`__impl_<Iface>_<Head>_<method>`) and routed
  through the normal function pipeline — so it is type-checked, certified, and
  code-generated with no bespoke machinery. The coherence registry then records
  `(iface, head) → %{method => mangled_atom}`; `Cure.Elab.Resolve` reads that map
  to inline a method at a concrete call site or thread a runtime dictionary at an
  abstract one.

  A method the instance omits is filled from the interface's default body, with
  the interface head variable substituted by this instance's head type (so the
  default's `a`-typed signature becomes concrete). A method with neither an
  instance clause nor a default is a `:missing_method` error.
  """

  alias Cure.Core.Env
  alias Cure.Elab.{Coherence, Declarations, Resolve}
  alias Cure.MetaAST.Metadata

  @doc """
  Register an implementation: build its mangled method defs, record the instance
  in the coherence registry, and register the method *signatures* in `env` (so
  forward references resolve). Returns the mangled `{:function_def, …}` decls for
  the caller to body-elaborate in the second pass, exactly like ordinary
  functions.
  """
  @spec register(tuple(), Env.t()) ::
          {:ok, Env.t(), [tuple()], [tuple()]} | {:error, term()}
  def register({:implementation, meta, body}, env) do
    iface = meta |> Keyword.fetch!(:interface) |> String.to_atom()
    for_type = Keyword.fetch!(meta, :for_type)
    for_name = surface_for_name(for_type, Keyword.get(meta, :for))
    as_name = Keyword.get(meta, :as)
    constraints = Keyword.get(meta, :constraints, [])
    implementation_span = implementation_header_span(meta)
    interface_span = implementation_interface_span(meta)
    interface_candidates = Map.keys(env.interfaces)

    with {:ok, head} <- head_key(for_type, env),
         desc when not is_nil(desc) <- Env.get_interface(env, iface),
         :ok <- check_no_stray_clauses(desc, iface, body),
         {:ok, method_map, mangled_fns} <-
           build_methods(desc, iface, head, for_name, for_type, body, implementation_span, constraints, env),
         # The ref lands in `env.coherence`, which is part of the semantic
         # environment: envs are compared for equality and published as frozen
         # module interfaces. `for_type` and `constraints` are raw surface ASTs,
         # so storing them verbatim carried spans and `source_info` into that
         # record, and an interface hash would then depend on where in the file
         # the `implementation` happened to sit — which is exactly the input an
         # incremental rebuild must not be sensitive to. Their only consumer,
         # `Cure.Elab.Resolve.bind_instance_type/3`, walks structure and never
         # reads metadata, so the semantic content is unchanged.
         ref = %{
           iface: iface,
           head: head,
           methods: method_map,
           as: as_name,
           for_type: Metadata.strip_diagnostics(for_type),
           constraints: Metadata.strip_diagnostics(constraints)
         },
         {:ok, env1} <-
           register_instance(env, iface, head, as_name, ref, %{
             interface: iface,
             head: head,
             for: for_name,
             span: implementation_span
           }),
         {:ok, env2} <- register_signatures(mangled_fns, env1),
         {:ok, env3} <- bind_named_instance(env2, desc, iface, head, as_name, ref) do
      {:ok, env3, mangled_fns, superinterface_obligations(iface, desc, head, for_name, implementation_span)}
    else
      nil ->
        {:error,
         {:no_such_interface,
          %{
            interface: iface,
            span: interface_span,
            candidates: interface_candidates
          }}}

      {:error, {:instance_head_ill_formed, details}} ->
        {:error,
         {:instance_head_ill_formed,
          Map.merge(details, %{
            interface: iface,
            for: for_name,
            span: implementation_type_span(meta)
          })}}

      {:error, _} = err ->
        err
    end
  end

  @doc """
  Resolve the coherence head key for `for_type_ast` in `env` (the same
  normalisation `register/2` keys an instance on). `{:ok, head}` or an error if the
  head is ill-formed. Used by the prelude-shadow strip to identify which ambient
  instances a module's own declarations supersede.
  """
  @spec head_of(Env.t(), tuple()) :: {:ok, atom()} | {:error, term()}
  def head_of(env, for_type_ast), do: head_key(for_type_ast, env)

  # The interfaces whose method bodies the COMPILER runs, rather than the program.
  # A contextual literal is elaborated by normalising the selected instance's
  # conversion to a canonical value, so these bodies are compile-time machinery in
  # the same sense a type synonym's RHS is.
  @compile_time_interfaces ~w(
    ExpressibleByNaturalLiteral
    ExpressibleByIntegerLiteral
    ExpressibleByDecimalLiteral
    ExpressibleByStringLiteral
    ExpressibleByCharacterLiteral
    ExpressibleByAtomLiteral
  )

  @doc """
  Whether `key` names an instance method the elaborator evaluates at compile time.

  A module interface hides definition bodies by default, which is right for
  ordinary code: a caller depends on a function's type, not its text. It is wrong
  for an instance the elaborator must REDUCE — `2` at `Int` is only a value
  because `from_integer_literal`'s body reduces to one, and an opaque body leaves
  the elaborator holding a stuck application it can only report as
  `:literal_initializer_not_compile_time_value`. Interface construction seeds
  transparency from this predicate, then closes over whatever those bodies mention.
  """
  @spec compile_time_method?(atom()) :: boolean()
  def compile_time_method?(key) when is_atom(key) do
    # Split on the FIRST `#` only — the qualifier separator. A mangled method
    # embeds the instance HEAD, which is itself qualified
    # (`Std.Literal#__impl_ExpressibleByIntegerLiteral_Std.Int#Int_from_integer_literal`),
    # so taking the last segment would strip the very prefix being matched.
    base =
      case key |> Atom.to_string() |> String.split("#", parts: 2) do
        [_owner, base] -> base
        [bare] -> bare
      end

    Enum.any?(@compile_time_interfaces, &String.starts_with?(base, "__impl_" <> &1 <> "_"))
  end

  # The coherence key: elaborate the instance head to a Core type, whnf it, and
  # read the head constructor's canonical name. Transparent synonyms unfold via
  # the kernel's δ-reduction of certified globals, so `MyInt = Int` keys as `:Int`.
  #
  # The parser sets `meta[:for]` to the RAW SURFACE NAME of the `for` clause, with no semantic
  # unfolding. `typealias MyInt = Int` is a transparent synonym at the type-checking level — the
  # two names denote definitionally the same type — but keying coherence on the spelling filed
  # `for Int` and `for MyInt` under two different atoms, so both anonymous instances registered.
  # Two live dictionaries for one type means `eq(x, y)` can compute two different answers
  # depending on which spelling of the type the call site happened to use. Idris, Agda, Lean and
  # Rust all resolve an instance head to its normal form before comparing, precisely to rule
  # this out. Routing through the kernel's `whnf_value` (rather than chasing surface `def` bodies
  # by hand) reuses the same certified δ-reduction the type checker trusts everywhere else.
  #
  # Registration and dispatch agree on which synonyms unfold. `whnf_value` with the default
  # `delta: :certified` δ-unfolds every certified global head; the dispatch classifier
  # (`Cure.Elab.Resolve.classify/3`) unfolds a nullary type-level def unconditionally. These
  # coincide for every synonym reachable from surface syntax: a synonym that reduces to a
  # concrete head (`typealias MyInt = Int`, and chains thereof) is non-recursive, so it is
  # certified the moment it is elaborated — before any `implementation` for it is registered —
  # and the certified δ-gate then unfolds it exactly as dispatch does. The only globals
  # `whnf_value` leaves folded that `classify` would unfold are non-total / not-yet-elaborated
  # ones, and those never reduce to a concrete head on EITHER path. So there is no certification
  # asymmetry to close here, and no delta option to pass: `whnf_value` offers only `:certified`
  # and `:none`, and `:certified` is already the liberality dispatch needs.
  #
  # On success returns `{:ok, atom}`; a lowering failure propagates as `{:error, reason}` so two
  # distinct malformed heads cannot silently collapse onto one sentinel key and misreport as an
  # overlapping instance.
  defp head_key(for_type_ast, env) do
    case Declarations.lower_type(for_type_ast, [], env) do
      {:ok, core_type} ->
        head =
          core_type
          |> Cure.Core.Eval.eval([])
          |> Cure.Core.Normalise.whnf_value(env, [])
          |> whnf_head_atom()

        case head do
          :non_type_head ->
            {:error, {:instance_head_ill_formed, %{reason: :not_type_head}}}

          atom ->
            {:ok, atom}
        end

      {:error, reason} ->
        {:error, {:instance_head_ill_formed, %{reason: :lowering_failed, underlying: reason}}}
    end
  end

  defp whnf_head_atom({:vint_type}), do: :Int
  defp whnf_head_atom({:vfloat_type}), do: :Float
  defp whnf_head_atom({:vbinary_type}), do: :Binary
  defp whnf_head_atom({:vatom_type}), do: :Atom
  # A universe, a Π/function type, and an inert `Effect(T)` are all legitimate (if exotic)
  # instance heads; key them by a descriptive atom rather than the raw Core value. Every
  # function type shares the `:Function` key — distinguishing them structurally is out of scope,
  # and function heads never dispatch statically (`classify/3` returns `:unknown` for a `vpi`).
  defp whnf_head_atom({:vtype, _level}), do: :Type
  defp whnf_head_atom({:vpi, _grade, _dom, _cod}), do: :Function
  defp whnf_head_atom({:veffect_type, _inner}), do: :Effect
  defp whnf_head_atom({:vdata, name, _args}), do: name
  # A stuck global (uncertified / open synonym) falls back to its own name — the
  # same behavior the old `head_atom` fallback gave.
  defp whnf_head_atom({:vneutral, {:nglobal, name}}), do: name
  # Any other Value former in head position is not a well-formed type head (a λ, a constructor
  # or primitive-literal VALUE, or a stuck var/application/eliminator). Return a sentinel ATOM —
  # never the raw Core term, which is not `String.Chars` and crashed `mangled_name`'s
  # interpolation. Such a head is itself ill-typed and rejected upstream; the sentinel only keeps
  # the key well-typed if one ever reaches here.
  defp whnf_head_atom(_other), do: :non_type_head

  # Every clause in the implementation body must name one of the interface's methods.
  # `build_methods/5` iterates the INTERFACE's `method_order` and searches the body by
  # exact name, so a clause naming nothing (a typo: `eqz` for `eqs`) was never looked
  # at — it contributed nothing and produced no diagnostic. If the method the author
  # meant to override had an interface default, the implementation registered anyway,
  # silently using the default and discarding the author's clause. Idris 2 rejects a
  # stray clause; so do we.
  defp check_no_stray_clauses(desc, iface, body) do
    declared = MapSet.new(desc.method_order, &Atom.to_string/1)

    body
    |> Enum.flat_map(fn
      {:function_def, m, _b} -> [{Keyword.fetch!(m, :name), m}]
      _ -> []
    end)
    |> Enum.find(fn {name, _meta} -> not MapSet.member?(declared, name) end)
    |> case do
      nil ->
        :ok

      {stray, member_meta} ->
        {:error,
         {:unknown_interface_method,
          %{
            interface: iface,
            method: String.to_atom(stray),
            candidates: desc.method_order,
            span: metadata_span(member_meta)
          }}}
    end
  end

  # A `interface Big(t) requires Small(t)` declaration obliges every
  # `implementation Big for T` to already have an `implementation Small for T`.
  # Rather than check the coherence registry here — which, during the sequential
  # registration fold, only holds implementations written EARLIER in source order
  # — we RECORD one `{iface, super_interface, head}` obligation per superinterface
  # and hand it back to the caller. `Cure.Elab.Program.body_register_pass` drains
  # every recorded obligation against the FINAL coherence table once all
  # implementations are registered, so `implementation Big for T` may textually
  # precede `implementation Small for T` (order-independent, matching Idris). An
  # interface with no `requires` clause has `super: []`, so this yields no
  # obligations. Older descriptors without the key default to `[]`.
  defp superinterface_obligations(iface, desc, head, for_name, span) do
    desc
    |> Map.get(:super, [])
    |> Enum.map(fn super_interface ->
      %{
        interface: iface,
        superinterface: super_interface,
        head: head,
        for: for_name,
        span: span
      }
    end)
  end

  # -- methods ----------------------------------------------------------------

  # For each interface method (in declaration order) produce a mangled global
  # function_def — either the instance's own clause renamed, or the interface
  # default specialised to this head type. Returns the `method => mangled_atom`
  # map alongside the decls.
  defp build_methods(desc, iface, head, for_name, for_type, body, implementation_span, constraints, env) do
    Enum.reduce_while(desc.method_order, {:ok, %{}, []}, fn method, {:ok, mm, fns} ->
      mangled = mangled_name(env, iface, head, method)

      with {:ok, fn_decl, origin} <- method_def(desc, method, for_type, body),
           :ok <- check_method_signature(desc, iface, method, for_type, fn_decl, origin, env) do
        renamed = rename_fn(fn_decl, mangled, constraints)
        {:cont, {:ok, Map.put(mm, method, mangled), fns ++ [renamed]}}
      else
        :missing ->
          {:halt,
           {:error,
            {:missing_method,
             %{
               interface: iface,
               method: method,
               head: head,
               for: for_name,
               span: implementation_span
             }}}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
  end

  # An instance clause for `method`, or the interface default specialised to the
  # instance's head type, or `:missing`. The tag says which — a default is synthesised
  # FROM the interface signature and so conforms by construction.
  defp method_def(desc, method, for_type, body) do
    mstr = Atom.to_string(method)

    case Enum.find(body, &function_def_named?(&1, mstr)) do
      {:function_def, _m, _b} = fd ->
        {:ok, fd, :instance}

      nil ->
        case Map.fetch(desc.defaults, mstr) do
          {:ok, default_body} ->
            {:ok, default_fn_def(desc, method, default_body, for_type), :default}

          :error ->
            :missing
        end
    end
  end

  # An implementation is a record literal, checked field-by-field against the record's
  # declared field types (Idris 2, Lean 4). Cure took the instance clause VERBATIM and
  # derived the mangled global's Pi type from the clause's OWN params/return_type, never
  # from the interface's. Nothing reconciled the two, so
  #
  #     interface Eqs(a)
  #       fn eqs(x: a, y: a) -> Bool
  #     implementation Eqs for Int
  #       fn eqs(x: Int, y: Int) -> Int = 42
  #
  # registered happily. Every USE site then failed with a bare
  # `{:conversion_failure, {:int_type}, {:data, :Bool, [], []}}` pointing at the caller
  # rather than at the implementation that broke its contract.
  #
  # The clause must declare the interface's signature with the head variable replaced by
  # this instance's head type, up to renaming of the method's other type variables
  # (`fmap`'s `a`/`b`). Lowercase-initial names are type variables and alpha-renamable;
  # uppercase names are type constructors and must match on the nose — the convention the
  # rest of the compiler already assumes.
  # A synthesized default conforms to the interface signature by construction.
  defp check_method_signature(_desc, _iface, _method, _for_type, _fn_decl, :default, _env), do: :ok

  # An instance clause must declare the interface method's type with the head
  # variable replaced by this instance's head type, up to definitional equality.
  # We elaborate both the expected (interface, head-substituted) and actual
  # (instance clause) function types to closed Core Pi types and compare with the
  # kernel's conversion — which handles α-renaming of the method's other type
  # variables and δ-unfolding of synonyms for free.
  defp check_method_signature(desc, iface, method, for_type, {:function_def, m, _b}, :instance, env) do
    info = Map.fetch!(desc.methods, method)

    expected_ast = subst_head(info.type_ast, desc.head_var, for_type)
    actual_ast = function_type_ast(Keyword.get(m, :params, []), Keyword.get(m, :return_type))

    # The method's OWN type variables (`fmap`'s `a`/`b`) are universally quantified
    # but written free in the surface AST. Bind each side's free type variables as a
    # positional de Bruijn scope so `lower_type` lowers them to `{:var, idx}` rather
    # than distinct global neutrals; a consistent renaming (`a`↔`x`, `b`↔`y`) then
    # lowers to identical Core terms and passes conversion, while a genuine type
    # mismatch stays distinct.
    # The expected signature was authored by the interface's module, not by this
    # one, so it is lowered in checking scope: a name the provider wrote resolves
    # because the provider could write it. The instance's own clause keeps the
    # authored scope, where naming a module this one never imported is still an
    # error — the asymmetry is the point.
    expected_env = checking_scope(env)
    # A derived clause is not authored either: the compiler chose its spelling
    # (`Std.Bool.Bool`, `Std.Builtin.struct_eq`), so it is held to the same scope
    # as the interface signature it was synthesised from, not to the module's.
    actual_env = if Keyword.get(m, :compiler_generated, false), do: expected_env, else: env

    expected_scope = Declarations.free_type_vars([expected_ast], expected_env)
    actual_scope = Declarations.free_type_vars([actual_ast], actual_env)

    with {:ok, expected_core} <- Declarations.lower_type(expected_ast, expected_scope, expected_env),
         {:ok, actual_core} <- Declarations.lower_type(actual_ast, actual_scope, actual_env),
         true <- Cure.Core.Conv.conv?(expected_core, actual_core, [], 0, env) do
      :ok
    else
      _ ->
        expected_core = lower_type_or_nil(expected_ast, expected_scope, expected_env)
        actual_core = lower_type_or_nil(actual_ast, actual_scope, actual_env)

        {:error,
         {:method_signature_mismatch,
          %{
            interface: iface,
            method: method,
            expected: expected_core,
            actual: actual_core,
            span: metadata_span(m)
          }}}
    end
  end

  # Every module present in the environment is nameable, which is what
  # "loadable for checking canonical references" means. This widens no authored
  # scope: it is used only to lower syntax the module under check did not write.
  defp checking_scope(%Env{} = env), do: %Env{env | qualified_modules: nil}

  defp lower_type_or_nil(ast, scope, env) do
    case Declarations.lower_type(ast, scope, env) do
      {:ok, core} -> core
      {:error, _reason} -> nil
    end
  end

  defp metadata_span(meta), do: meta |> Cure.MetaAST.Metadata.source_info() |> source_info_span()
  defp source_info_span(%Cure.MetaAST.SourceInfo{whole: span}), do: span
  defp source_info_span(_source_info), do: nil

  defp implementation_header_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{opener: %Cure.Diagnostic.Span{} = opener} = source_info ->
        ending =
          [source_info.name, source_info.annotation | Map.values(source_info.fields || %{})]
          |> Enum.filter(&match?(%Cure.Diagnostic.Span{}, &1))
          |> Enum.max_by(& &1.end_byte, fn -> opener end)

        %Cure.Diagnostic.Span{
          opener
          | end_byte: ending.end_byte,
            end_line: ending.end_line,
            end_column: ending.end_column
        }

      source_info ->
        source_info_span(source_info)
    end
  end

  defp implementation_type_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{annotation: %Cure.Diagnostic.Span{} = span} -> span
      _source_info -> implementation_header_span(meta)
    end
  end

  defp implementation_interface_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
      _source_info -> implementation_header_span(meta)
    end
  end

  defp surface_for_name({:literal, _meta, value}, _fallback) when is_integer(value),
    do: Integer.to_string(value)

  defp surface_for_name({:literal, _meta, value}, _fallback) when is_float(value),
    do: Float.to_string(value)

  defp surface_for_name(_for_type, fallback), do: fallback

  # Build the surface function-type AST `T1 -> ... -> Tn -> R` from a param list
  # and return type, MIRRORING `Interface.build_method_map`'s `method_type_ast`
  # (interface.ex:140-143) EXACTLY — a single flat `{:function_call,
  # [function_type: true], [doms..., result]}` node — so the two lower to the same
  # Core Pi chain and kernel conversion sees identical structure.
  defp function_type_ast(params, return_type) do
    dom_asts = Enum.map(params, fn {:param, pm, _pname} -> Keyword.fetch!(pm, :type) end)
    {:function_call, [function_type: true], dom_asts ++ [return_type]}
  end

  defp function_def_named?({:function_def, m, _body}, name), do: Keyword.get(m, :name) == name
  defp function_def_named?(_other, _name), do: false

  # Synthesise a concrete function_def from the interface method's signature and
  # the default body, substituting the head variable with the instance's head
  # type in every parameter/return type.
  defp default_fn_def(desc, method, default_body, for_type) do
    info = Map.fetch!(desc.methods, method)
    head_var = desc.head_var

    params =
      Enum.map(info.params, fn {:param, pm, pname} ->
        {:param, Keyword.put(pm, :type, subst_head(Keyword.fetch!(pm, :type), head_var, for_type)), pname}
      end)

    return_type = subst_head(info.return_type, head_var, for_type)

    meta = [
      name: info.name,
      params: params,
      return_type: return_type,
      visibility: :public,
      arity: length(params)
    ]

    {:function_def, meta, [default_body]}
  end

  # Replace every occurrence of the head variable in a type AST with `for_type`, in BOTH
  # positions it can occupy: bare (`x : a`, first-order interface) and applied
  # (`container : f(a)`, higher-kinded — where the head name lives in the node's meta,
  # not among its children). Missing the applied case left `f(a)` unsubstituted, which
  # both mis-specialised a higher-kinded interface DEFAULT and made signature checking
  # impossible.
  defp subst_head({:variable, _m, name}, head_var, for_type) when name == head_var, do: for_type
  defp subst_head({:variable, _m, _} = v, _head_var, _for_type), do: v

  defp subst_head({:function_call, m, args}, head_var, for_type) do
    args = Enum.map(args, &subst_head(&1, head_var, for_type))

    case {Keyword.get(m, :name), type_ctor_name(for_type)} do
      {^head_var, ctor} when is_binary(ctor) and is_binary(head_var) ->
        {:function_call, Keyword.put(m, :name, ctor), args}

      _ ->
        {:function_call, m, args}
    end
  end

  defp subst_head(other, _head_var, _for_type), do: other

  defp type_ctor_name({:variable, _m, name}), do: name
  defp type_ctor_name(_other), do: nil

  defp rename_fn({:function_def, m, b}, mangled, constraints) do
    meta =
      m
      |> Keyword.put(:name, Atom.to_string(mangled))
      |> Keyword.update(:constraints, constraints, &(constraints ++ &1))

    {:function_def, meta, b}
  end

  defp mangled_name(env, iface, head, method) do
    base = :"__impl_#{iface}_#{head}_#{method}"

    case Env.owner(env) do
      nil -> base
      owner -> Cure.Elab.Name.qualify(owner, base)
    end
  end

  # -- registration -----------------------------------------------------------

  defp register_instance(env, iface, head, as_name, ref, origin) do
    coherence = Env.coherence(env) || Coherence.new()

    result =
      case as_name do
        nil -> Coherence.register_anon(coherence, iface, head, ref, origin)
        name -> Coherence.register_named(coherence, String.to_atom(name), {iface, head}, ref, origin)
      end

    case result do
      {:ok, coherence1} -> {:ok, Env.put_coherence(env, coherence1)}
      {:error, _} = err -> err
    end
  end

  # Cure's coherence policy is global uniqueness plus NAMED implementations as the escape hatch:
  # `implementation Eqs for Int as strictInt` registers under `:strictInt` "as an ordinary
  # dictionary-valued binding… A caller selects it explicitly with plain record projection,
  # `strictInt.eqs(x, y)` … no new call syntax is needed".
  #
  # `register_instance/5` only wrote the ref into `Coherence.named`. Nothing ever bound the atom
  # `:strictInt` to a value, and `Coherence.lookup_named/2` had zero callers in lib/ — so there
  # was no path by which any reference to `strictInt` could resolve. The escape hatch the policy
  # depends on to let a second, overlapping instance coexist was accepted at register time and
  # then permanently unreachable. Binding it as an ordinary global of type `Iface(head)` is what
  # makes record projection find it.
  #
  # A higher-kinded interface has no Core dictionary record family to be a value of
  # (`Interface.declare_dictionary_former/2` builds one only for a `:type` head kind), so there
  # is nothing to bind; that gap is tracked with the abstract-dispatch gap it belongs to.
  defp bind_named_instance(env, _desc, _iface, _head, nil, _ref), do: {:ok, env}

  defp bind_named_instance(env, %{head_kind: :type}, iface, head, name, ref) do
    term = Resolve.dict_term_from_ref(env, iface, ref)
    {:ok, Env.add_def(env, String.to_atom(name), Resolve.dict_type_term(env, iface, head), term)}
  end

  defp bind_named_instance(env, _desc, _iface, _head, _name, _ref), do: {:ok, env}

  defp register_signatures(fn_decls, env) do
    Enum.reduce_while(fn_decls, {:ok, env}, fn fd, {:ok, acc} ->
      case Declarations.register_signature(fd, acc) do
        {:ok, acc2} -> {:cont, {:ok, acc2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end
end
