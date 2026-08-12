defmodule Cure.Elab.Declarations do
  @moduledoc """
  Elaborate surface type declarations into `Cure.Core` inductive families
  (design spec §5; mirrors Idris `TTImp/ProcessData.idr`).

  Untrusted: it builds candidate `Inductive.family`/`Inductive.ctor` signatures
  and submits them to the kernel (`check_family`/`check_ctor` + strict
  positivity), so only well-formed families are registered.

  Handles the surface ADT form the parser produces today —
  `type X = A(T) | B | …` (`{:container, [container_type: :enum, …], variants}`).
  The family's universe level is inferred as the least level (0..ceiling) at
  which every constructor field type fits (the two-universe rule, §2): a field of
  type `Type` pushes the family to level 1. Indexed-GADT surface syntax
  (`indexed type … where`) is a separate parser extension (not yet in the
  grammar); the kernel-side indexed-family machinery it targets is complete (M3).
  """

  alias Cure.Core.{Context, Env, Eval, Grade, Inductive, Kernel, Quote, Term}
  alias Cure.Elab.{Elaborator, Induction, MacroExpand, MetaCtx, Relevance, Subst, Unify}
  alias Cure.MetaAST.Metadata

  @ceiling 2

  # The runtime classes an `@erases(<class>)` may name. Each maps to exactly one TOTAL
  # Erlang guard in `Cure.Elab.Emit.class_guard/1`, which is what makes an opaque
  # carrier discriminable inside an anonymous union.
  @erasure_classes [:pid, :reference, :integer, :float, :binary, :atom, :boolean, :list]

  @doc """
  The admissible `@erases(<class>)` set. Exposed for `Cure.Compiler.Errors`, which
  names it in the `:unknown_erasure_class` message rather than duplicating the list.
  """
  @spec erasure_classes() :: [atom()]
  def erasure_classes, do: @erasure_classes

  @doc """
  Elaborate one declaration AST, returning the augmented signature.

  Runs the anonymous-union pre-pass first: every `{:union_type, …}` node anywhere in
  this declaration has its generated family declared into `env` BEFORE lowering, so
  that `idx_to_core/5` — which returns `{:ok, term}` and cannot thread a mutated
  `Env` back out — only has to look the content-derived key up.
  """
  @spec elaborate(tuple(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def elaborate(decl, env) do
    result =
      with :ok <- reject_erases_on_non_opaque(decl),
           {:ok, env} <- Cure.Elab.Union.predeclare_all(decl, env) do
        do_elaborate(decl, env)
      end

    attach_declaration_source_context(result, decl)
  end

  defp do_elaborate({:function_def, _meta, _body} = decl, env) do
    with {:ok, env1} <- register_signature(decl, env) do
      elaborate_function_body(decl, env1)
    end
  end

  defp do_elaborate({:container, meta, variants}, env) do
    case Keyword.get(meta, :container_type) do
      :enum ->
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()

        # Enum ADT (`type List(a) = Nil | Cons(a, List(a))`, or `type Nat = Z | S(Nat)`).
        # Each positional variant is an implicit constructor signature returning the
        # family applied to its own parameters; reuse the parameterized-family (GADT)
        # machinery with an empty index telescope.
        #
        # The zero-type-param case used to have its own `build_ctors/1` pipeline, a
        # strict subset of `idx_to_core/5` with no arrow clause — so a function-typed
        # field was rejected for `type Callback = Wrap((Int) -> Int)` while the
        # semantically identical `rec Callback` and `type Callback(a) = ...` both
        # accepted it. That was duplication producing an arbitrary feature gap, not a
        # deliberate restriction; a negative occurrence is still rejected, by
        # `Inductive.positive?/2` where it belongs.
        with :ok <- reject_reserved_family_name(name) do
          type_params = Keyword.get(meta, :type_params, [])
          params = Enum.map(type_params, fn p -> {:param, [], p} end)
          sigs = Enum.map(variants, &variant_to_gadt_sig(&1, name, type_params))
          declare_parameterized(name, params, [], sigs, env)
        end

      :struct ->
        # A record `rec Point\n  x: T\n  y: U` is a single-constructor family whose
        # constructor shares the family name and whose argument telescope is named by
        # the fields. The field names carried on the constructor telescope are what
        # record construction (`Point{x: .., y: ..}`) and projection (`p.x`) read to
        # map names to positions — no separate registry, and the kernel treats the
        # argument names as plain labels.
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()

        with :ok <- reject_reserved_family_name(name),
             :ok <- check_no_duplicate_fields(variants) do
          case Keyword.get(meta, :type_params, []) do
            [] ->
              # Route through the GADT-ctor machinery with NAMED field domains so a
              # field's type may reference an EARLIER field (a dependent record):
              # `elaborate_gadt_ctor`'s named-binder scope-threading binds each field
              # name for subsequent field types. Non-dependent records are unaffected —
              # the resulting ctor telescope is still named by the fields, which is what
              # construction/projection read.
              sig = struct_ctor_sig(name, [], variants)
              working_env = Inductive.declare(env, Inductive.family(name, [], [], 0), [])

              with {:ok, [ctor]} <- elaborate_gadt_ctors([sig], name, [], [], working_env) do
                declare_at_min_level(env, name, [attach_field_defaults(ctor, variants)], 0)
                |> register_record_field_sites(env, name, variants)
              end

            type_params ->
              declare_parameterized_struct(name, type_params, variants, env)
              |> register_record_field_sites(env, name, variants)
          end
        end

      :opaque ->
        # `opaque type Name(params)` — a constructor-less, non-eliminable carrier
        # family. Elaborate the parameter telescope (each `a : Type0`), then
        # register a family MARKED opaque with zero constructors. No ctor or
        # positivity checks (there are none); the marker makes the kernel refuse
        # to eliminate it (Agda `postulate`).
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()

        params =
          Keyword.get_lazy(meta, :params, fn ->
            Keyword.get(meta, :type_params, []) |> Enum.map(fn p -> {:param, [], p} end)
          end)

        with :ok <- reject_reserved_family_name(name),
             {:ok, erasure} <- erasure_class(meta, name),
             {:ok, param_tele} <-
               elaborate_index_telescope(params, name, env, [], :duplicate_parameter) do
          declare_opaque_at_min_level(env, name, param_tele, 0, erasure)
        end

      :primitive ->
        # `@builtin(:tag) primitive Name` — read the marker, map it to a Core
        # node, and confirm the binding against the seeded floor (rejecting a
        # missing marker, an unknown tag, or a tag that disagrees with the floor).
        name = Keyword.get(meta, :name)

        with {:ok, tag} <- primitive_builtin_tag(meta),
             {:ok, node} <- primitive_tag_node(tag),
             :ok <- confirm_primitive_floor(env, name, node) do
          {:ok, Env.put_primitive(env, name, node)}
        end

      other ->
        {:error, {:unsupported_container, other}}
    end
  end

  # Indexed (GADT) family: `type NAME(params) indices (idx) <ctor sigs>`. Head
  # `(params)` are uniform parameters (restated, never matched); the `indices`
  # clause lists the refined indices. Each constructor signature is an
  # `{:arrow_chain, meta, [dom…, result]}`; the implicit index-variable telescope is
  # inferred from the signature (§5.2). A parameter-free family omits `(params)`.
  # `type X = Y` with a single bare right-hand side is ambiguous, and the parser cannot
  # resolve it — it tags the RHS `variant: true` and defers:
  #
  #   type MyNat = Nat          -- an ALIAS: `Nat` names a type in scope
  #   type Unit = MkUnit        -- a one-constructor ENUM: `MkUnit` names no type
  #
  # (`typealias X = Y` is never a variant, and `type X = A | B` already parses as an
  # `:enum` container.) Resolve on whether the RHS names a type. Getting this wrong used
  # to be invisible: the alias branch installed `Unit := {:data, :MkUnit, [], []}` with a
  # hardcoded kind and nothing ever checked it, so a one-constructor enum silently became
  # an alias to a family that does not exist.
  defp do_elaborate({:type_annotation, meta, [rhs]} = decl, env) do
    if single_variant_enum?(rhs, env) do
      elaborate({:container, Keyword.put(meta, :container_type, :enum), [rhs]}, env)
    else
      elaborate_typealias(decl, env)
    end
  end

  defp do_elaborate({:indexed_type, meta, ctor_sigs}, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()

    with :ok <- reject_reserved_family_name(name) do
      params = Keyword.get(meta, :params, [])
      index_params = Keyword.get(meta, :indices, [])
      declare_parameterized(name, params, index_params, ctor_sigs, env)
    end
  end

  defp do_elaborate({:interface, _meta, _methods} = decl, env) do
    Cure.Elab.Interface.elaborate(decl, env)
  end

  defp do_elaborate(other, _env) when is_tuple(other),
    do: {:error, {:unsupported_declaration, elem(other, 0)}}

  defp do_elaborate(other, _env), do: {:error, {:unsupported_declaration, declaration_shape(other)}}

  # Declaration validation runs after parsing and can also receive generated
  # MetaAST. Preserve the exact authored declaration role when one exists,
  # while leaving generated-only failures honestly span-free.
  defp attach_declaration_source_context(
         {:error, reason},
         {:container, meta, _children}
       )
       when is_list(meta) and
              elem(reason, 0) in [
                :primitive_missing_builtin,
                :unknown_primitive_tag,
                :primitive_floor_mismatch
              ] do
    info = Cure.MetaAST.Metadata.source_info(meta)
    kind = elem(reason, 0)

    context = %{
      span: primitive_failure_span(kind, info),
      declaration_span: if(info, do: info.whole),
      name_span: if(info, do: info.name),
      builtin_span: decorator_span(info, "builtin", :whole),
      builtin_argument_span: decorator_span(info, "builtin", 0),
      primitive: Keyword.get(meta, :name),
      builtin_tag: primitive_decorator_tag(meta),
      expectation_origin: :primitive_declaration,
      expression_category: :primitive_declaration
    }

    {:error, {:source_context, reason, context}}
  end

  defp attach_declaration_source_context(
         {:error, {:unsupported_declaration, _shape} = reason},
         {_tag, meta, _children}
       )
       when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{} = info ->
        {:error,
         {:source_context, reason,
          %{
            span: info.whole,
            declaration_span: info.whole,
            name_span: info.name,
            expectation_origin: :declaration_validation,
            expression_category: :declaration
          }}}

      _ ->
        {:error, reason}
    end
  end

  defp attach_declaration_source_context(
         {:error, {:source_context, {:result_type_not_family, _family}, context} = reason},
         {:indexed_type, meta, _constructors}
       )
       when is_list(meta) and is_map(context) do
    info = Cure.MetaAST.Metadata.source_info(meta)

    {:error,
     {:source_context, elem(reason, 1),
      Map.merge(
        %{
          family_declaration_span: info && info.whole,
          family_name_span: info && info.name,
          family: Keyword.get(meta, :name),
          expectation_origin: :constructor_result,
          expression_category: :constructor_signature
        },
        context
      )}}
  end

  defp attach_declaration_source_context(result, _decl), do: result

  defp primitive_failure_span(kind, info)
       when kind in [:unknown_primitive_tag, :primitive_floor_mismatch],
       do: decorator_span(info, "builtin", 0) || if(info, do: info.name)

  defp primitive_failure_span(_kind, info), do: if(info, do: info.name || info.whole)

  defp decorator_span(%Cure.MetaAST.SourceInfo{decorators: decorators}, name, :whole) do
    case Map.get(decorators, name) do
      %{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  defp decorator_span(%Cure.MetaAST.SourceInfo{decorators: decorators}, name, index)
       when is_integer(index) do
    case Map.get(decorators, name) do
      %{arguments: arguments} -> Enum.at(arguments, index)
      _ -> nil
    end
  end

  defp decorator_span(_info, _name, _role), do: nil

  defp primitive_decorator_tag(meta) do
    case Keyword.get(meta, :decorator) do
      {:decorator, dm, [{:literal, _, tag}]} when is_atom(tag) ->
        if Keyword.get(dm, :name) == :builtin, do: tag

      _ ->
        nil
    end
  end

  defp declaration_shape(value) when is_map(value), do: :map
  defp declaration_shape(value) when is_list(value), do: :list
  defp declaration_shape(value) when is_atom(value), do: value
  defp declaration_shape(_value), do: :unknown

  # `Cure.Elab.Union.union_family?/1` recognises a generated union family purely
  # by a name-prefix test ("Union<…>"). That is safe only if the prefix is truly
  # unproducible by a user-authored type name — but backtick-quoted identifiers
  # (`lexer.ex` `lex_quoted_identifier/1`) admit ANY character, including `<`,
  # `>`, and `|`, and nothing upstream of here restricts which lexing form
  # produced a type-declaration name. Left unchecked, a user type named e.g.
  # `` `Union<Bool|Int>` `` would be indistinguishable from a compiler-generated
  # family to every union-aware code path (flattening in `Cure.Elab.Union`,
  # injection/widening in the elaborator) — reject it here, at the one point
  # every user-declared family name passes through, so the reserved namespace is
  # actually enforced rather than merely assumed.
  @spec reject_reserved_family_name(atom()) :: :ok | {:error, {:reserved_union_type_name, atom()}}
  defp reject_reserved_family_name(name) do
    if Cure.Elab.Union.reserved_name?(name) do
      {:error, {:reserved_union_type_name, name}}
    else
      :ok
    end
  end

  # Every constructor a declaration introduces shares ONE global flat namespace with the
  # generated union constructors (`env.ctors`, an unconditional Map.put). A backtick ctor
  # named `Union<Int|String>$Int` would silently overwrite the real one.
  defp reject_reserved_ctor_names(sigs) do
    Enum.find_value(sigs, :ok, fn {:gadt_ctor, cmeta, _chain} ->
      cname = Keyword.fetch!(cmeta, :name)

      if Cure.Elab.Union.reserved_name?(cname) do
        {:error, {:reserved_union_type_name, String.to_atom(cname)}}
      end
    end)
  end

  @doc """
  Register a type family's HEADER — its name and parameter/index telescopes with
  an EMPTY constructor list — WITHOUT elaborating its constructor bodies.

  `Program.register_pass` runs this over every declaration in a module before it
  elaborates any constructor body, so a field type may name a sibling declared
  later (forward reference) or a mutually-recursive partner. The authoritative
  declaration — same header, real constructors — still happens in the main pass
  via `elaborate/2`, which re-declares the family (`Inductive.declare` is a plain
  keyed put, so re-registering the header with the real ctors simply overwrites
  the empty placeholder).

  Constructor-bearing families and explicit transparent aliases participate.
  Alias headers contain only the name and erased type-parameter telescope; the
  checked RHS replaces the body-less placeholder in the main pass. `@builtin`
  containers are skipped because canonical builtin registration owns them.
  """
  @spec declare_header(term(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def declare_header({:container, meta, _variants}, env) when is_list(meta) do
    cond do
      # An OPAQUE carrier is checked before the `@builtin` skip below. That skip is
      # for families the kernel seeds from `Cure.Core.Builtins`, where the source
      # declaration only names an identity that already exists. A constructor-less
      # carrier is the opposite case: the source is its sole definition, and a
      # builtin key merely says which kernel rule may introduce its values
      # (`@builtin(:char) opaque type Char`). Skipping it here left `Char` invisible
      # to `Std.Literal` — its own SCC peer, which types `CharacterLiteral`'s field
      # by it — so the field resolved to a bare unknown global.
      Keyword.get(meta, :container_type) == :opaque ->
        # Opaque carriers participate in interface SCCs exactly like ordinary
        # families: peer signatures must be able to mention the nominal type
        # before either module's bodies are elaborated. Register the complete
        # constructor-less family here (including its declared erasure class).
        # The ordinary declaration pass installs the same canonical family
        # again, so this is an idempotent header rather than a second identity.
        elaborate({:container, meta, []}, env)

      attached_decorator_name(Keyword.get(meta, :decorator)) == :builtin ->
        {:ok, env}

      Keyword.get(meta, :container_type) in [:enum, :struct] ->
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()

        with :ok <- reject_reserved_family_name(name) do
          params = Keyword.get(meta, :type_params, []) |> Enum.map(fn p -> {:param, [], p} end)
          register_header(name, params, [], env)
        end

      true ->
        {:ok, env}
    end
  end

  def declare_header({:indexed_type, meta, _ctor_sigs}, env) when is_list(meta) do
    if attached_decorator_name(Keyword.get(meta, :decorator)) == :builtin do
      {:ok, env}
    else
      name = meta |> Keyword.fetch!(:name) |> String.to_atom()
      params = Keyword.get(meta, :params, [])
      index_params = Keyword.get(meta, :indices, [])
      register_header(name, params, index_params, env)
    end
  end

  # A bare single right-hand side (`type B = MkB`) parses as `:type_annotation`
  # and is a single-constructor enum when the RHS names no existing type (the
  # same disambiguation `elaborate/2` makes). Register its header so an earlier
  # sibling may forward-reference it; a genuine typealias (`type MyNat = Nat`)
  # binds a nullary def, not a ctor-bearing family, so it is left to the main
  # pass.
  def declare_header({:type_annotation, meta, [rhs]}, env) when is_list(meta) do
    cond do
      Keyword.get(meta, :typealias, false) ->
        register_typealias_header(meta, env)

      single_variant_enum?(rhs, env) ->
        name = meta |> Keyword.fetch!(:name) |> String.to_atom()
        params = Keyword.get(meta, :type_params, []) |> Enum.map(fn p -> {:param, [], p} end)
        register_header(name, params, [], env)

      true ->
        {:ok, env}
    end
  end

  # An `interface` header must exist before any sibling declaration that mentions
  # it — a `requires` clause, a constrained signature, or an `implementation` — so
  # it is registered in the header pre-pass rather than waiting for source order.
  def declare_header({:interface, meta, _methods} = decl, env) when is_list(meta),
    do: Cure.Elab.Interface.elaborate(decl, env)

  def declare_header(_decl, env), do: {:ok, env}

  # A forward alias needs only a well-sorted name while signatures and earlier
  # aliases are lowered. Its real universe and transparent body are unknown
  # until the main pass, which overwrites this entry. Type parameters are
  # uniformly erased `Type 0` binders, matching `elaborate_typealias/2`.
  defp register_typealias_header(meta, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()

    params = typealias_params(meta)

    with :ok <- reject_reserved_family_name(name),
         {:ok, telescope, quantities, _scope} <- elaborate_param_telescope(params, env) do
      # A nullary alias names an ordinary small type. Giving its placeholder
      # the ceiling universe makes every signature that mentions it infer
      # `Type2` until the real RHS overwrites the entry, which is too late for
      # an interface SCC (for example `Char = Bounded(...)` <-> `String`).
      result_sort = if telescope == [], do: {:type, 0}, else: {:type, @ceiling}
      type = wrap_binders(:pi, telescope, quantities, result_sort)
      {:ok, Env.add_def(env, name, type, nil, quantities)}
    end
  end

  # Elaborate the parameter/index telescopes (mirroring `declare_parameterized`'s
  # prefix) and register the family with an empty constructor list.
  defp register_header(name, params, index_params, env) do
    param_scope = params |> Enum.map(fn {:param, _m, n} -> n end) |> Enum.reverse()

    with {:ok, param_tele} <-
           elaborate_index_telescope(params, name, env, [], :duplicate_parameter),
         {:ok, index_tele} <- elaborate_index_telescope(index_params, name, env, param_scope) do
      {:ok, Inductive.declare(env, Inductive.family(name, param_tele, index_tele, 0), [])}
    end
  end

  defp single_variant_enum?({:variable, rmeta, name}, env) when is_list(rmeta) and is_binary(name),
    do: Keyword.get(rmeta, :variant, false) and not type_name?(env, name)

  defp single_variant_enum?(_rhs, _env), do: false

  # Does `name` denote a type in `env`? A builtin primitive, a declared family, the
  # universe itself, or an earlier alias (a def whose declared type is a universe).
  defp type_name?(_env, "Type"), do: true

  defp type_name?(env, name) do
    atom = String.to_atom(name)

    Env.primitive(env, name) != nil or
      Inductive.get_family(env, atom) != nil or
      match?(%{type: {:type, _}}, Env.get_def(env, atom))
  end

  # Type alias `typealias Name(params?) = RHS`: a transparent definition whose
  # parameters are erased Pi/lambda binders. Conversion δ-unfolds the alias to
  # its right-hand side (a non-recursive alias is trivially total, so it
  # certifies and δ becomes available). No new type former.
  #
  # The RHS must BE a type. It used to be installed with a hardcoded declared type of
  # `{:type, 0}`, and the only kernel check that ever ran on it was `maybe_certify/2` —
  # whose whole job is to swallow errors, because for a FUNCTION body a failure there
  # means only "does not certify as total, so stop δ-unfolding it", never "ill-typed"
  # (the body's `Kernel.check/3` already ran and its error was propagated). A typealias
  # has no such prior check, so `validate_certificate/2` was its first and only one, and
  # a genuine kind error was discarded exactly like a benign non-termination verdict.
  # `typealias Bad = Z` aliased `Bad` to a Nat CONSTRUCTOR and reported `{:ok, _}`. Idris
  # (`Bad : Type; Bad = Z`) and Lean (`def Bad : Type := Z`) both reject it outright.
  #
  # Infer the RHS's type and demand a universe, then register the alias at THAT level —
  # `typealias U = Type` is legal and lives at `Type 1`, not `Type 0`.
  defp elaborate_typealias({:type_annotation, meta, [rhs]}, env) do
    name = meta |> Keyword.fetch!(:name) |> String.to_atom()

    params = typealias_params(meta)

    with :ok <- reject_reserved_family_name(name),
         {:ok, telescope, quantities, scope} <- elaborate_param_telescope(params, env),
         ctx = build_context(env, telescope),
         {:ok, rhs_core} <- idx_to_core(rhs, scope, nil, env),
         {:ok, level} <- typealias_universe(ctx, name, rhs_core, meta, rhs) do
      type_core = wrap_binders(:pi, telescope, quantities, {:type, level})
      body = wrap_binders(:lam, telescope, quantities, rhs_core)
      env1 = env |> Env.add_def(name, type_core, body, quantities) |> Env.put_typealias(name)
      {:ok, maybe_certify(env1, name)}
    end
  end

  defp typealias_universe(ctx, name, rhs_core, meta, rhs) do
    case Kernel.infer(ctx, rhs_core) do
      {:ok, {:vtype, level}} ->
        {:ok, level}

      {:ok, other} ->
        info = Cure.MetaAST.Metadata.source_info(meta)
        rhs_info = rhs |> elem(1) |> Cure.MetaAST.Metadata.source_info()

        {:error,
         {:typealias_not_a_type,
          %{
            name: name,
            actual_type: Quote.reify(other, 0),
            rhs_shape: typealias_rhs_shape(rhs),
            span: rhs_info && rhs_info.whole,
            declaration_span: info && info.whole,
            name_span: info && info.name
          }}}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp typealias_rhs_shape({tag, _meta, _children}) when is_atom(tag), do: tag
  defp typealias_rhs_shape(_rhs), do: :expression

  defp typealias_params(meta) do
    meta
    |> Keyword.get_lazy(:params, fn ->
      Keyword.get(meta, :type_params, []) |> Enum.map(fn p -> {:param, [], p} end)
    end)
    |> Enum.map(fn
      {:param, pmeta, name} ->
        type = Keyword.get(pmeta, :type, {:variable, [scope: :local], "Type"})
        {:param, Keyword.put(pmeta, :type, type), name}
    end)
  end

  defp maybe_certify(env, name) do
    case Kernel.validate_certificate(env, name) do
      {:ok, certified} -> certified
      {:error, _} -> env
    end
  end

  # Elaborate a function's signature to its Π type and register it (with a
  # placeholder body) so that later-defined functions and mutually-recursive peers
  # resolve as globals. Called for every function in a first pass, before any body
  # is elaborated (see `Program.elaborate_declarations`).
  #
  # Runs the anonymous-union pre-pass first. `Program.body_register_pass/3` routes
  # `{:function_def, …}` here rather than through `elaborate/2`, and a function
  # signature is the commonest place a union appears — so the pre-pass must hook
  # BOTH entry points. It walks the whole declaration AST, so a union in a `let`
  # annotation inside the body is covered here too, and it is idempotent (the
  # content-derived key is guarded by `Inductive.family?`), so the double hook is
  # free.
  def register_signature({:function_def, _meta, _body} = decl, env) do
    with {:ok, env} <- Cure.Elab.Union.predeclare_all(decl, env) do
      do_register_signature(decl, env)
    end
  end

  defp do_register_signature({:function_def, meta, _body}, env) do
    with :ok <- validate_extern_typed_head(meta),
         {:ok, sig} <- function_signature(meta, env) do
      env1 =
        env
        |> Env.add_def(sig.name, sig.pi, {:hole, "__pending__"}, sig.quantities, sig.plicities)
        # Labels must ride the record from the SIGNATURE pass on: overlap legality
        # (`check_overload_legality`) runs between the signature and body passes and
        # needs them to tell `move(to:)` from `move(from:)`. The body pass re-adds
        # the def (dropping this) and re-attaches its own copy.
        |> Env.put_labels(sig.name, param_label_vector(sig.params))
        |> register_parameter_spans(sig.name, sig.params)
        |> register_declaration_span(sig.name, meta)
        |> maybe_register_unsafe(sig.name, meta)
        |> maybe_register_lemma(sig, meta)

      env2 =
        case sig.constraints do
          [] -> env1
          specs -> Env.put_constrained(env1, sig.name, specs)
        end

      {:ok, env2}
    end
  end

  # Elaborate a function's body against its (already registered) signature and
  # replace the placeholder with the real lambda. The environment already carries
  # every function's signature, so forward references and mutual recursion resolve.
  def elaborate_function_body(decl, env, opts \\ [])

  def elaborate_function_body({:function_def, _meta, _body} = decl, env, opts) do
    {:function_def, meta, body} = desugar_clause_fn(decl)

    case Keyword.get(meta, :extern) do
      {mod, fun, arity} when is_atom(mod) and is_atom(fun) and is_integer(arity) ->
        # Wave-3: a bodyless @extern is a typed FFI postulate — the signature IS
        # the type; there is no term to elaborate/check. Mark the def with an
        # extern sentinel (NOT a hole, so emit.reject_holes passes; NOT
        # builtin_op, which is overloaded). emit lowers it to a remote call;
        # TotalityClosure skips it. Do NOT call elaborate_body / Kernel.check /
        # Relevance.check (no term exists).
        with :ok <- reject_extern_body(meta, body),
             {:ok, sig} <- function_signature(meta, env),
             :ok <- check_extern_arity(sig, arity),
             :ok <- check_extern_not_union(sig, env) do
          final =
            env
            |> Env.add_def(sig.name, sig.pi, {:extern, {mod, fun, arity}}, sig.quantities, sig.plicities)
            |> Env.put_labels(sig.name, param_label_vector(sig.params))
            |> register_parameter_spans(sig.name, sig.params)
            |> maybe_register_unsafe(sig.name, meta)

          {:ok, final}
        end

      _ ->
        elaborate_real_body(meta, body, env, opts)
    end
  end

  defp validate_extern_typed_head(meta) do
    if Keyword.has_key?(meta, :extern) do
      untyped_param =
        meta
        |> Keyword.get(:params, [])
        |> Enum.find(fn
          {:param, param_meta, _name} when is_list(param_meta) -> not Keyword.has_key?(param_meta, :type)
          _ -> false
        end)

      cond do
        untyped_param ->
          {:param, param_meta, _name} = untyped_param
          extern_source_error(:extern_untyped_head, "Every `@extern` parameter needs an explicit type.", param_meta)

        not Keyword.has_key?(meta, :return_type) ->
          extern_source_error(:extern_untyped_head, "Every `@extern` function needs an explicit result type.", meta)

        true ->
          :ok
      end
    else
      :ok
    end
  end

  defp reject_extern_body(_meta, []), do: :ok

  defp reject_extern_body(meta, [first | _]) do
    body_meta = if match?({_tag, child_meta, _children} when is_list(child_meta), first), do: elem(first, 1), else: meta

    extern_source_error(
      :extern_has_body,
      "An `@extern` declaration is supplied by its foreign target and cannot also define a Cure body.",
      body_meta
    )
  end

  defp reject_extern_body(meta, _body) do
    extern_source_error(
      :extern_has_body,
      "An `@extern` declaration is supplied by its foreign target and cannot also define a Cure body.",
      meta
    )
  end

  defp extern_source_error(kind, message, meta) do
    span =
      case Cure.MetaAST.Metadata.source_info(meta) do
        %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = name} -> name
        %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = whole} -> whole
        _ -> nil
      end

    location =
      if span,
        do: [line: span.start_line, col: span.start_column, length: max(1, span.end_byte - span.start_byte)],
        else: []

    reason = {kind, message, location}

    if span do
      {:error,
       {:source_context, reason,
        %{
          span: span,
          expectation_origin: :ffi_boundary,
          expression_category: :extern_declaration
        }}}
    else
      {:error, reason}
    end
  end

  # The arity in `@extern(:mod, :fun, arity)` names the TARGET Erlang function — `erlang:hd/1`.
  # Erased parameters never reach the BEAM, so that number is also exactly the def's present
  # arity, which is what `Emit` gives the generated function and what every Cure call site passes
  # (`Emit.present_arity/2`, off the same `quantities`). Nothing used to force the two to agree.
  #
  # An extern with an erased implicit — `head({T: Type}, xs: List(T))`, and auto-generalization
  # inserts one for any free lowercase type var even when the user writes none — has a present
  # arity strictly below its surface telescope length. A user counting the parens writes 2, and
  # `Emit` then generated `head/2` calling `erlang:hd(V0, V1)` while every Cure caller invoked
  # `head/1`. Each form compiled in isolation; the module was broken the moment anything called
  # it. Rejecting the mismatch is the only reading under which the number means one thing.
  # An `@extern` is a typed FFI postulate: Erlang hands back a RAW value carrying no
  # constructor tag. A union-returning extern is therefore only meaningful if the boundary
  # RE-TAGS the value — which `Emit.extern_form/4` does, by guarding on the raw result and
  # injecting the matching constructor.
  #
  # That is sound only when the members are pairwise distinguishable from an untagged
  # value. Members sharing an erased shape (`Int`/`Nat`/`Char` are all Erlang integers;
  # `Bool` erases to `true`/`false` so it collides with `Atom`; `String` IS `List(Char)`)
  # cannot be told apart, and are rejected HERE, at the declaration the author can see,
  # rather than miscompiling into a CaseClauseError at the first use.
  #
  # The ARGUMENT direction needs no check: passing a union INTO Erlang hands it an
  # ordinary tagged tuple, which is a perfectly good Erlang term.
  #
  # A leading `Effect` is STRIPPED first. `Effect(T)` has no runtime representation — it
  # erases to `T` exactly (`Emit.lower/3` drops `{:effect_pure, …}`) — so an effectful
  # extern returning a union hands back the very same untagged value a pure one does, and
  # takes the very same re-tagging wrapper. Only the HEAD is stripped, so a union buried
  # inside the effect's payload (`Effect(List(Int | Binary))`) is still rejected below.
  defp check_extern_not_union(sig, env) do
    codomain =
      sig.pi
      |> extern_codomain(length(sig.quantities || []))
      |> strip_effect()

    case codomain do
      {:data, ukey, [], []} ->
        if Cure.Elab.Union.union_family?(ukey) do
          case Cure.Elab.Union.discriminable(Cure.Elab.Union.members_of(env, ukey), env) do
            :ok ->
              :ok

            {:error, reason} ->
              {:error,
               extern_union_source_context(
                 {:extern_union_indistinct, sig.name, reason},
                 sig,
                 env,
                 [ukey]
               )}
          end
        else
          :ok
        end

      _ ->
        # A union NESTED inside the return type (`List(Int | Bool)`) cannot be re-tagged:
        # the boundary would have to walk an arbitrary structure. Reject.
        if Elaborator.union_goal?(codomain) do
          {:error,
           extern_union_source_context(
             {:extern_returns_union, sig.name, codomain},
             sig,
             env,
             nested_union_families(codomain)
           )}
        else
          :ok
        end
    end
  end

  defp extern_union_source_context(reason, sig, env, families) do
    union_members =
      families
      |> Enum.flat_map(&Cure.Elab.Union.members_of(env, &1))
      |> Enum.map(& &1.key)
      |> Enum.uniq()

    {:source_context, reason,
     %{
       span: sig.return_span || sig.declaration_span,
       return_span: sig.return_span,
       declaration_span: sig.declaration_span,
       name_span: sig.name_span,
       extern_span: sig.extern_span,
       checking: sig.name,
       expectation_origin: :ffi_boundary,
       expression_category: :extern_return_type,
       union_families: families,
       union_members: union_members
     }}
  end

  defp nested_union_families({:data, family, parameters, indices}) do
    own = if Cure.Elab.Union.union_family?(family), do: [family], else: []
    own ++ Enum.flat_map(parameters ++ indices, &nested_union_families/1)
  end

  defp nested_union_families(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.flat_map(&nested_union_families/1)

  defp nested_union_families(list) when is_list(list), do: Enum.flat_map(list, &nested_union_families/1)
  defp nested_union_families(_other), do: []

  defp extern_codomain(type, 0), do: type
  defp extern_codomain({:pi, _g, _dom, cod}, n), do: extern_codomain(cod, n - 1)
  defp extern_codomain(type, _n), do: type

  # `Effect(T)` erases to `T`, so the RESULT SHAPE an FFI boundary sees is `T`'s. One
  # layer only: `Effect` is not nestable in the surface language.
  @doc false
  def strip_effect({:effect_type, t}), do: t
  def strip_effect(type), do: type

  defp check_extern_arity(sig, arity) do
    # PRESENT, not unrestricted. Slice 4a's rename left `== :unrestricted` here, which
    # excludes `:linear`/`:affine` parameters — they have runtime values and DO reach
    # the BEAM, so they must be counted. Same trap 4a fixed in `Erase`/`Emit` and 4b
    # fixed in `Relevance`.
    present = Enum.count(sig.quantities || [], &Grade.present?/1)

    if arity == present do
      :ok
    else
      {:error,
       {:extern_arity_mismatch,
        %{
          name: sig.name,
          declared: arity,
          present: present,
          span: sig.extern_arity_span
        }}}
    end
  end

  # Multi-clause function-head syntax — `fn f(n) | 0 -> a | n -> b` — parses to a
  # `{:function_def, [clauses: [...]], []}` whose body lives in `meta[:clauses]`
  # (one `%{guard, params, body}` per clause) and whose top-level body is empty.
  # The dependent pipeline elaborates a single body, so desugar the clauses into a
  # `match` over the formal parameters: the scrutinee is the sole parameter (or a
  # flat tuple `%[p1, …, pN]` of them), each clause becomes a `:match_arm` whose
  # pattern is the clause's parameter pattern (or their tuple) and whose optional
  # `when`-guard rides through as the arm guard. A def with no `clauses:` key is
  # returned unchanged, so ordinary `fn f(x) = …` bodies are untouched. Signature
  # registration reads `meta[:params]`/`:return_type`/`:name` and ignores the body,
  # so it needs no desugaring.
  defp desugar_clause_fn({:function_def, meta, _body} = decl) do
    case Keyword.get(meta, :clauses) do
      [_ | _] = clauses ->
        formals = Keyword.get(meta, :params, [])
        fmeta = generated_meta(meta)
        scrut = clause_scrutinee(formals, fmeta)
        arms = Enum.map(clauses, &clause_to_arm(&1, length(formals), fmeta))
        match_expr = {:pattern_match, fmeta, [scrut | arms]}
        {:function_def, Keyword.delete(meta, :clauses), [match_expr]}

      _ ->
        decl
    end
  end

  defp generated_meta(meta) when is_list(meta) do
    Keyword.take(meta, [
      :line,
      :col,
      :column,
      :source_info,
      :provenance,
      :source_provenance,
      :expansion_provenance
    ])
  end

  defp clause_scrutinee([{:param, _pm, pname}], fmeta),
    do: {:variable, [scope: :local] ++ fmeta, pname}

  defp clause_scrutinee(formals, fmeta),
    do: {:tuple, fmeta, Enum.map(formals, fn {:param, _pm, pname} -> {:variable, [scope: :local] ++ fmeta, pname} end)}

  defp clause_to_arm(%{guard: guard, params: pats, body: cbody} = clause, arity, fmeta) do
    pattern = if arity == 1, do: hd(pats), else: {:tuple, fmeta, pats}
    arm_meta = [pattern: pattern] ++ if(guard, do: [guard: guard], else: [])
    arm_meta = put_clause_source_info(arm_meta, Map.get(clause, :source_info))
    {:match_arm, arm_meta, cbody}
  end

  defp put_clause_source_info(meta, %Cure.MetaAST.SourceInfo{} = info),
    do: Cure.MetaAST.Metadata.put_source_info(meta, info)

  defp put_clause_source_info(meta, _), do: meta

  defp elaborate_real_body(meta, body, env, opts) do
    body_expr = single_body(body)

    with {:ok, body_expr} <-
           timed_body_stage(opts, :macro_expansion, fn ->
             MacroExpand.expand(body_expr, env, callback_context: Keyword.get(meta, :callback_context))
           end),
         {:ok, sig} <- timed_body_stage(opts, :signature, fn -> function_signature(meta, env) end),
         {:ok, body_expr} <-
           timed_body_stage(opts, :induction, fn -> Induction.expand(body_expr, sig, env) end) do
      ctx = build_context(env, sig.telescope, sig.quantities)
      # Qualify any hole minted while elaborating THIS body by its enclosing def
      # (`hole_id/2`) — local to this call, never merged back into `final` below,
      # so it cannot leak into another def's elaboration.
      def_env = Env.with_current_def(env, sig.name)

      with {:ok, body_term, return_core, _return_value} <-
             timed_body_stage(opts, :typed_elaboration, fn ->
               elaborate_body_typed(body_expr, sig, ctx, def_env)
             end),
           # A `where`-introduced dictionary parameter is present by default but
           # SAFELY demoted to `:erased` when the body never uses it relevantly (an
           # `ignore`-style constrained function): the same criterion the relevance
           # check enforces, so erasure (dropping it) stays sound. Only demotion,
           # never promotion.
           quantities = demote_unused_dicts(env, sig, body_term),
           # {0,ω} relevance check (M8.3): erasure will drop the `:erased` parameter
           # slots, so reject any body that uses one relevantly (returned / passed
           # in a present position / scrutinised / applied). E-layer; the kernel
           # stays quantity-blind. See `Cure.Elab.Relevance`.
           :ok <- Relevance.check(env, sig.name, quantities, body_term),
           # The Pi is the single source of truth (slice 6). `sig.pi` was built from
           # the ORIGINAL quantities; `demote_unused_dicts/3` may have lowered a dict
           # since, so rebuild the stored type from the DEMOTED vector — otherwise the
           # stored Pi (dict `ω`) and λ (dict `:erased`) would disagree, a pairing the
           # graded `Conv` forbids. Both now come from one vector.
           final_pi = wrap_binders(:pi, sig.telescope, quantities, return_core),
           lambda = wrap_binders(:lam, sig.telescope, quantities, body_term),
           # The assertion that would have caught the whole dichotomy class: the stored
           # Π and λ must agree on every binder's grade. Compare the two grade spines
           # STRUCTURALLY — do NOT re-run a full `Kernel.check` of the body. The body
           # already type-checked at `:284` against `build_context`'s WHNF'd context; a
           # second kernel check here would rebuild the context WITHOUT that whnf (the
           # `:lam` rule's `Context.extend` does not normalise `exp_dom`), so a
           # parameter whose type is a δ-unfoldable alias reaches the kernel as an
           # opaque neutral and a `match` on it fails `:case_scrutinee_not_data` — a
           # regression the first cut of this slice shipped (adversarial review F1).
           # The grade check is all slice 6 needs, and it is O(telescope depth).
           :ok <- assert_binder_grades_agree(final_pi, lambda, sig.name),
           # §5.3: an `Effect`-typed binder may not be `:erased`. Erasure deletes
           # erased binders, so an erased `Effect(T)` binder would silently drop a
           # computation the type says must run. Walk the final Pi spine and reject.
           # (Syntactic head-check; the `no_effect_in_erased_position` Validator
           # clause is the trusted backstop for an aliased effect type, §8.)
           :ok <- assert_no_erased_effect_binder(final_pi, sig.name) do
        final =
          env
          |> Env.add_def(sig.name, final_pi, lambda, quantities, sig.plicities)
          |> maybe_register_unsafe(sig.name, meta)
          |> maybe_register_reducible(sig.name, meta)
          |> Env.put_source_holes(sig.name, collect_source_holes(body_expr, def_env, sig.return_span))
          |> Env.put_labels(sig.name, param_label_vector(sig.params))
          |> register_parameter_spans(sig.name, sig.params)

        # Best-effort totality certification, eagerly and in declaration order, so a
        # later def's type may δ-reduce this one (e.g. `plus` in `Vec(a, plus(m,n))`
        # must unfold while `append`'s body is checked). A function that fails the
        # kernel's totality check simply stays uncertified — opaque to δ, never a
        # soundness hole (§7). Whole-program enforcement of the *required* set still
        # happens in TotalityClosure.certify_type_level.
        final = maybe_certify(final, sig.name)
        Cure.Elab.Equation.generate(final, sig.name, meta, body_expr)
      end
    end
  end

  defp timed_body_stage(opts, stage, operation) when is_function(operation, 0) do
    started = System.monotonic_time(:microsecond)
    result = operation.()
    elapsed = System.monotonic_time(:microsecond) - started

    case Keyword.get(opts, :event_sink) do
      sink when is_function(sink, 2) -> emit_body_stage_timing(sink, stage, elapsed)
      _ -> :ok
    end

    result
  end

  defp emit_body_stage_timing(sink, stage, elapsed) do
    sink.(stage, elapsed)
    :ok
  rescue
    _ -> :ok
  catch
    _, _ -> :ok
  end

  defp maybe_register_unsafe(env, name, meta) do
    case Keyword.get(meta, :decorator) do
      {:decorator, decorator_meta, _args} when is_list(decorator_meta) ->
        Env.put_unsafe(env, name, Keyword.get(decorator_meta, :name) == :unsafe)

      _ ->
        env
    end
  end

  # `@reducible` publishes this body in the module's canonical interface, so a
  # consumer may δ-unfold it. Marking is the author's call because the provider
  # cannot see who will reason about it: `Std.Proof.LinearArithmetic.Semantics`
  # states `evaluate_atom(normalize_atom(a), v) == evaluate_atom(a, v)`, and that
  # theorem is unprovable unless both functions compute one module away.
  defp maybe_register_reducible(env, name, meta) do
    case Keyword.get(meta, :decorator) do
      {:decorator, decorator_meta, _args} when is_list(decorator_meta) ->
        Env.put_reducible(env, name, Keyword.get(decorator_meta, :name) == :reducible)

      _ ->
        env
    end
  end

  defp collect_source_holes(ast, env, annotation_span) do
    collect_source_holes(ast, env, annotation_span, %{})
  end

  defp collect_source_holes({:hole, meta, children}, env, annotation_span, acc) when is_list(meta) do
    info = Cure.MetaAST.Metadata.source_info(meta)
    span = if info, do: info.whole

    acc =
      Map.put(acc, hole_id(env, meta), %{
        span: span,
        annotation_span: annotation_span
      })

    collect_source_holes(children, env, annotation_span, acc)
  end

  defp collect_source_holes({tag, meta, children}, env, annotation_span, acc)
       when is_atom(tag) and is_list(meta) do
    acc = collect_source_holes(meta, env, annotation_span, acc)
    collect_source_holes(children, env, annotation_span, acc)
  end

  defp collect_source_holes(list, env, annotation_span, acc) when is_list(list),
    do: Enum.reduce(list, acc, &collect_source_holes(&1, env, annotation_span, &2))

  defp collect_source_holes(tuple, env, annotation_span, acc) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> collect_source_holes(env, annotation_span, acc)

  defp collect_source_holes(map, env, annotation_span, acc) when is_map(map) and not is_struct(map),
    do: map |> Map.values() |> collect_source_holes(env, annotation_span, acc)

  defp collect_source_holes(_other, _env, _annotation_span, acc), do: acc
  # Elaborate the body and settle the return type + its Core form. With a DECLARED
  # return, check the body against it (the long-standing behavior). With NONE
  # (annotation-free `fn f() = expr`, which the parser accepts), INFER the body's
  # type and adopt it as the codomain — `function_signature/2` left a `{:type, 0}`
  # placeholder that this replaces. Inference carries no expected-type flow, so an
  # annotation-free body whose type is pinned only by a return-only implicit still
  # needs an explicit signature; every REPL/`:let` wrapper returns a concrete type,
  # which is exactly the case this serves. Returns `{body_term, return_core,
  # return_value}` so the caller rebuilds the final Π from the settled codomain.
  defp elaborate_body_typed(body_expr, %{inferred_return: true} = sig, ctx, env) do
    with {:ok, body_term, ret_val} <-
           attach_source_context(
             Elaborator.elaborate_expr_typed(body_expr, sig.scope, ctx, env),
             body_expr,
             sig.name,
             env,
             nil
           ) do
      ret_core = Quote.reify(ret_val, length(sig.telescope))
      {:ok, body_term, ret_core, ret_val}
    end
  end

  defp elaborate_body_typed(body_expr, sig, ctx, env) do
    return_value = Eval.eval(sig.return_core, Context.env(ctx))

    with {:ok, body_term} <-
           attach_source_context(
             elaborate_declared_body(body_expr, sig.return_core, sig.scope, ctx, env, sig.params),
             body_expr,
             sig.name,
             env,
             sig.return_span
           ),
         :ok <-
           attach_source_context(
             Kernel.check_with_branch_details(ctx, body_term, return_value),
             body_expr,
             sig.name,
             env,
             sig.return_span
           ) do
      {:ok, body_term, sig.return_core, return_value}
    end
  end

  defp attach_source_context({:error, reason}, expression, checking, env, expectation_span) do
    reason = Elaborator.contextualize_call_arity(reason, expression, env)
    {line, column, length} = expression_extent(expression)
    meta = expression_meta(expression)
    source_info = Cure.MetaAST.Metadata.source_info(meta)

    expectation_origin =
      if branch_type_reason?(reason) and dependent_match?(expression, env),
        do: :dependent_branch,
        else: :annotation

    outer_context = %{
      line: line,
      column: column,
      length: length,
      checking: checking,
      span: if(source_info, do: source_info.whole),
      opener_span: if(source_info, do: source_info.opener),
      scrutinee_span: if(source_info, do: List.first(source_info.operands)),
      proof_span: if(source_info, do: Map.get(source_info.fields, :proof_clause)),
      proof_keyword_span: if(source_info, do: Map.get(source_info.fields, :proof_keyword)),
      proof_name_span: if(source_info, do: Map.get(source_info.fields, :proof_name)),
      proof_name: Keyword.get(meta, :proof),
      parameter_sites:
        env
        |> Env.owned_name(checking)
        |> Cure.Elab.SourceMetadata.parameter_sites(),
      expectation_span: expectation_span,
      expression_category: expression_category(expression),
      expectation_origin: expectation_origin,
      branch_patterns: branch_patterns(expression, env)
    }

    outer_context = declaration_expectation_context(expression, reason, outer_context, env)

    case reason do
      {:source_context, nested_reason, nested_context} when is_map(nested_context) ->
        # A checking-site producer may already know a more precise authored span
        # (for example the literal used as an `if` guard). Keep the declaration
        # context as a fallback, but never let its whole-body span overwrite the
        # nested source caret or expectation origin.
        merged_context = Map.merge(outer_context, nested_context)

        merged_context =
          if Map.get(outer_context, :expectation_origin) == :ffi and
               Map.get(nested_context, :expectation_origin) in [:call_result, :application] do
            Map.merge(merged_context, %{
              checking: Map.get(outer_context, :checking),
              expectation_origin: :ffi,
              expression_category: :function_call
            })
          else
            merged_context
          end

        merged_context =
          if expectation_span &&
               (Map.get(merged_context, :expectation_origin) == :annotation or
                  match?({:unsolved_metavariables, _}, nested_reason)) do
            Map.put(merged_context, :expectation_span, expectation_span)
          else
            merged_context
          end

        merged_context =
          case Map.get(merged_context, :span) do
            %Cure.Diagnostic.Span{} = span ->
              Map.merge(merged_context, %{
                line: span.start_line,
                column: span.start_column,
                length: max(1, span.end_column - span.start_column)
              })

            _ ->
              merged_context
          end

        {:error, {:source_context, nested_reason, merged_context}}

      _ ->
        {:error, {:source_context, reason, outer_context}}
    end
  end

  defp attach_source_context(result, _expression, _checking, _env, _expectation_span), do: result

  defp declaration_expectation_context({:function_call, meta, _args}, reason, context, env)
       when is_list(meta) do
    if projection_failure?(reason) do
      context
    else
      {origin, owner} =
        if ffi_call_failure?(reason, meta, env) do
          {:ffi, Keyword.get(meta, :name, context.checking)}
        else
          if implicit_failure?(reason) do
            {:implicit, Keyword.get(meta, :name, context.checking)}
          else
            if Keyword.has_key?(meta, :callee) do
              {:application, declaration_application_owner(meta)}
            else
              {:call_result, Keyword.get(meta, :name, context.checking)}
            end
          end
        end

      Map.merge(context, %{
        checking: owner,
        expectation_origin: origin,
        expression_category: :function_call
      })
    end
  end

  defp declaration_expectation_context({:binary_op, meta, _args}, reason, context, _env)
       when is_list(meta) and is_map(context) do
    if implicit_failure?(reason) do
      Map.merge(context, %{
        checking: Keyword.get(meta, :operator, context.checking),
        expectation_origin: :implicit,
        expression_category: :binary_op
      })
    else
      context
    end
  end

  defp declaration_expectation_context(_expression, _reason, context, _env), do: context

  defp projection_failure?({:source_context, _reason, %{expectation_origin: :projection}}), do: true
  defp projection_failure?(_reason), do: false

  defp ffi_call_failure?({:source_context, reason, _context}, meta, env),
    do: ffi_call_failure?(reason, meta, env)

  defp ffi_call_failure?(reason, meta, env) do
    name = Keyword.get(meta, :name)
    key = if is_binary(name), do: String.to_atom(name), else: name

    ffi_type_mismatch?(reason) and match?(%{body: {:extern, _}}, Env.get_def(env, key))
  end

  defp ffi_type_mismatch?({:cannot_unify, _actual, _expected}), do: true
  defp ffi_type_mismatch?({:index_mismatch, {:cannot_unify, _actual, _expected}}), do: true
  defp ffi_type_mismatch?({:conversion_failure, _actual, _expected}), do: true
  defp ffi_type_mismatch?(_reason), do: false

  defp implicit_failure?({:source_context, reason, _context}), do: implicit_failure?(reason)

  defp implicit_failure?({kind, _details}) when kind in [:unsolved_metavariables, :no_instance], do: true
  defp implicit_failure?({:no_instance, _interface, _head}), do: true
  defp implicit_failure?({:no_named_instance, _name}), do: true
  defp implicit_failure?(_reason), do: false

  defp declaration_application_owner(meta) do
    case Keyword.get(meta, :callee) do
      {:function_call, inner_meta, _args} when is_list(inner_meta) ->
        Keyword.get(inner_meta, :name, :application)

      _ ->
        :application
    end
  end

  defp expression_meta({_kind, meta, _children}) when is_list(meta), do: meta
  defp expression_meta({_kind, meta, _left, _right}) when is_list(meta), do: meta
  defp expression_meta(_expression), do: []

  defp expression_category({kind, _meta, _children}) when is_atom(kind), do: kind
  defp expression_category({kind, _meta, _left, _right}) when is_atom(kind), do: kind
  defp expression_category(_expression), do: :expression

  defp branch_patterns({:pattern_match, _meta, [_scrutinee | arms]}, env) do
    Enum.map(arms, &branch_pattern(&1, env))
  end

  defp branch_patterns({:with_abs, _meta, [_scrutinee | arms]}, env),
    do: Enum.map(arms, &branch_pattern(&1, env))

  defp branch_patterns(_expression, _env), do: []

  defp branch_pattern({family, arm_meta, _body}, env)
       when family in [:match_arm, :with_rematch_arm] and is_list(arm_meta) do
    pattern = Keyword.get(arm_meta, :pattern)

    %{
      name: pattern_label(pattern),
      kind: pattern_kind(pattern, env),
      family: family,
      span: arm_span(arm_meta),
      pattern_span: surface_pattern_span(arm_meta, pattern),
      guard_span:
        case Cure.MetaAST.Metadata.source_info(arm_meta) do
          %Cure.MetaAST.SourceInfo{guard: %Cure.Diagnostic.Span{} = span} -> span
          _ -> nil
        end,
      variable_spans: pattern_variable_spans(pattern)
    }
  end

  defp branch_pattern(_arm, _env), do: %{name: "unknown branch", span: nil}

  defp branch_type_reason?(:branch_type), do: true
  defp branch_type_reason?({:branch_type, _details}), do: true
  defp branch_type_reason?({:source_context, reason, _context}), do: branch_type_reason?(reason)
  defp branch_type_reason?(_reason), do: false

  defp dependent_match?({:pattern_match, _meta, [_scrutinee | arms]}, env) do
    Enum.any?(arms, fn
      {:match_arm, arm_meta, _body} ->
        with name when not is_nil(name) <- pattern_constructor(Keyword.get(arm_meta, :pattern)),
             key <- Env.resolve_key(env, env.ctors, name),
             family when not is_nil(family) <- Inductive.ctor_family(env, key),
             %{indices: indices} <- Inductive.get_family(env, family) do
          indices != []
        else
          _ -> false
        end

      _ ->
        false
    end)
  end

  defp dependent_match?(_expression, _env), do: false

  defp pattern_constructor({:function_call, meta, _args}) when is_list(meta) do
    case Keyword.get(meta, :name) do
      name when is_binary(name) -> String.to_atom(name)
      name -> name
    end
  end

  defp pattern_constructor({:variable, _meta, name}) when is_binary(name), do: String.to_atom(name)
  defp pattern_constructor(_pattern), do: nil

  defp pattern_label({:function_call, meta, _args}) when is_list(meta),
    do: meta |> Keyword.get(:name, "constructor") |> to_string()

  defp pattern_label({:variable, _meta, name}), do: to_string(name)
  defp pattern_label({:wildcard, _meta}), do: "_"
  defp pattern_label({:literal, _meta, value}), do: inspect(value)
  defp pattern_label(_pattern), do: "pattern"

  defp pattern_kind({:variable, _meta, name}, env) when is_binary(name) do
    key = Env.resolve_key(env, env.ctors, String.to_atom(name))
    if Inductive.get_ctor(env, key), do: :constructor, else: :variable
  end

  defp pattern_kind({:function_call, _meta, _args}, _env), do: :constructor
  defp pattern_kind(_pattern, _env), do: :other

  defp arm_span(meta) when is_list(meta) do
    case Keyword.get(meta, :source_info) do
      %Cure.MetaAST.SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  defp surface_pattern_span(meta, pattern) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{pattern: %Cure.Diagnostic.Span{} = span} -> span
      _ -> expression_meta(pattern) |> Cure.MetaAST.Metadata.source_info() |> then(&if(&1, do: &1.whole))
    end
  end

  defp pattern_variable_spans({:variable, meta, name}) when is_list(meta) and name != "_" do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> %{to_string(name) => [span]}
      _ -> %{}
    end
  end

  defp pattern_variable_spans({_tag, _meta, children}), do: pattern_variable_spans(children)

  defp pattern_variable_spans(items) when is_list(items) do
    Enum.reduce(items, %{}, fn item, acc ->
      Map.merge(acc, pattern_variable_spans(item), fn _name, left, right -> left ++ right end)
    end)
  end

  defp pattern_variable_spans(item) when is_tuple(item),
    do: item |> Tuple.to_list() |> pattern_variable_spans()

  defp pattern_variable_spans(_item), do: %{}

  defp expression_extent({_, meta, _} = expression) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} ->
        {span.start_line, span.start_column, max(1, span.end_column - span.start_column)}

      _ ->
        coordinate_extent(expression)
    end
  end

  defp expression_extent({_, meta, _, _} = expression) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} ->
        {span.start_line, span.start_column, max(1, span.end_column - span.start_column)}

      _ ->
        coordinate_extent(expression)
    end
  end

  defp expression_extent(expression) do
    coordinate_extent(expression)
  end

  defp coordinate_extent(expression) do
    meta = expression_meta(expression)
    {Keyword.get(meta, :line), Keyword.get(meta, :col), nil}
  end

  defp elaborate_declared_body(body_expr, return_core, scope, ctx, env, params) do
    if Elaborator.effect_goal?(return_core, ctx) do
      Elaborator.elaborate_effect_branch(body_expr, return_core, scope, ctx, env)
    else
      elaborate_body(body_expr, return_core, scope, ctx, env, params)
    end
  end

  # The signature's codomain Core term. A declared `-> T` is elaborated normally; an
  # omitted return (annotation-free `fn`) gets a `{:type, 0}` placeholder that
  # `elaborate_body_typed/4` overwrites with the inferred body type.
  defp signature_return_core(nil, _scope, _env, _ctx), do: {:ok, {:type, 0}}

  defp signature_return_core(return_expr, scope, env, ctx),
    do: idx_to_core(return_expr, scope, nil, env, ctx)

  # Shared signature elaboration: auto-generalize free type variables, build the
  # parameter telescope and the Π type. Deterministic in the type environment, so
  # the signature computed in the registration pass and the body pass agree.
  defp function_signature(meta, env) do
    # A member of an overload set (tagged with :overload_ordinal by
    # `annotate_overload_ordinals/1`) registers under a discriminated bare name
    # `plus~<ord>`; `Env.add_def`'s `owned_name` then qualifies it to
    # `Mod#plus~<ord>`. An untagged def keeps its plain bare name (inert).
    base_name = meta |> Keyword.fetch!(:name) |> String.to_atom()

    name =
      case Keyword.get(meta, :overload_ordinal) do
        nil -> base_name
        ord -> Cure.Elab.Name.overload_key(base_name, ord)
      end

    params0 = Keyword.get(meta, :params, [])
    # The parser makes `-> Type` optional (`fn f() = expr`); when omitted the
    # `:return_type` key is absent. An annotation-free function's codomain is
    # INFERRED from its body in `elaborate_real_body/3`; here it gets a placeholder
    # so `sig.pi` is well-formed for the pre-body registration pass (the final Pi is
    # rebuilt from the inferred return once the body is elaborated). `inferred_return`
    # flags that path.
    return_expr = Keyword.get(meta, :return_type)

    # Idris-style auto-generalization: a free lowercase type variable in the
    # signature (`fn id(x: a) -> a`) is bound as a leading implicit `{a: Type}`
    # (erased), in order of first appearance. Restricted to occurrences provably of
    # kind Type, so an index variable (`Vec(_, n)`, `n : Nat`) is NOT mis-bound.
    params1 = auto_generalize(params0, return_expr, env) ++ params0

    # A `where Iface(a)` clause introduces a runtime dictionary parameter typed by
    # the interface's record former (`Eqs(a)`), appended AFTER the value params so
    # the applicator has solved `a` from an earlier argument before it checks the
    # dictionary (and so its de-Bruijn index is stable). `constraint_specs` tells a
    # concrete call site which argument fixes `a` and how to name the dict binder.
    {params, constraint_specs} =
      inject_constraint_dicts(params1, Keyword.get(meta, :constraints, []), return_expr)

    source_info = Cure.MetaAST.Metadata.source_info(meta)

    with {:ok, telescope, quantities, scope} <- elaborate_param_telescope(params, env),
         ctx = build_context(env, telescope),
         {:ok, return_core} <- signature_return_core(return_expr, scope, env, ctx) do
      {:ok,
       %{
         name: name,
         params: params,
         telescope: telescope,
         quantities: quantities,
         plicities:
           Enum.map(params, fn {:param, pmeta, _} ->
             if Keyword.get(pmeta, :implicit, false), do: :implicit, else: :explicit
           end),
         scope: scope,
         return_core: return_core,
         return_span: function_return_span(meta),
         declaration_span: source_info && source_info.whole,
         name_span: source_info && source_info.name,
         extern_span: source_info && decorator_span(source_info, "extern", :whole),
         extern_arity_span: decorator_argument_span(meta, "extern", 2),
         inferred_return: is_nil(return_expr),
         constraints: constraint_specs,
         # The PRE-REGISTRATION type, honest about the ORIGINAL quantities (implicit
         # ⇒ erased). `demote_unused_dicts/3` may lower a dict below this after the
         # body is seen; the final stored Pi is rebuilt from the demoted vector so it
         # agrees with the λ (see `elaborate_function_body`).
         pi: wrap_binders(:pi, telescope, quantities, return_core)
       }}
    end
  end

  defp function_return_span(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{annotation: %Cure.Diagnostic.Span{} = span} ->
        span

      _ ->
        return_type_span(Keyword.get(meta, :return_type))
    end
  end

  defp return_type_span({_tag, meta, children}) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> children |> return_type_child_spans() |> cover_source_spans()
    end
  end

  defp return_type_span(_other), do: nil

  defp return_type_child_spans(children) when is_list(children),
    do: Enum.flat_map(children, &List.wrap(return_type_span(&1)))

  defp return_type_child_spans(_children), do: []

  defp cover_source_spans([]), do: nil

  defp cover_source_spans(spans) do
    first = Enum.min_by(spans, & &1.start_byte)
    last = Enum.max_by(spans, & &1.end_byte)

    %{first | end_byte: last.end_byte, end_line: last.end_line, end_column: last.end_column}
  end

  defp decorator_argument_span(meta, decorator, index) do
    with %Cure.MetaAST.SourceInfo{decorators: decorators} <- Cure.MetaAST.Metadata.source_info(meta),
         %{arguments: arguments} <- Map.get(decorators, decorator),
         %Cure.Diagnostic.Span{} = span <- Enum.at(arguments, index) do
      span
    else
      _ -> nil
    end
  end

  # Turn each `where Iface(a)` constraint into an implicit-style dictionary
  # parameter `__dict_Iface_a : Iface(a)`, appended to the telescope. Returns the
  # extended parameter list and a spec per constraint recording either the
  # explicit value parameter that fixes `a` (`head_arg_index`) or, when there is
  # none, the result shape from which checking mode can recover it.
  defp inject_constraint_dicts(params, [], _return_expr), do: {params, []}

  defp inject_constraint_dicts(params, constraints, return_expr) do
    explicit_value_params =
      Enum.filter(params, fn {:param, m, _n} -> not Keyword.get(m, :implicit, false) end)

    {dict_params, specs} =
      constraints
      |> Enum.map(fn {:function_call, cm, [tyvar_ast]} ->
        iface_str = Keyword.fetch!(cm, :name)
        iface_atom = String.to_atom(iface_str)
        {:variable, _, tyvar} = tyvar_ast
        dict_name = "__dict_#{iface_str}_#{tyvar}"

        direct_idx =
          Enum.find_index(explicit_value_params, fn {:param, pm, _n} ->
            match?({:variable, _, ^tyvar}, Keyword.get(pm, :type))
          end)

        idx =
          direct_idx ||
            Enum.find_index(explicit_value_params, fn {:param, pm, _n} ->
              type_ast_mentions_variable?(Keyword.get(pm, :type), tyvar)
            end)

        head_arg_type =
          if is_integer(idx) do
            {:param, pm, _name} = Enum.at(explicit_value_params, idx)
            Keyword.get(pm, :type)
          else
            nil
          end

        dparam =
          {:param, [type: {:function_call, [name: iface_str], [tyvar_ast]}, constraint_dict: {iface_atom, tyvar}],
           dict_name}

        # These descriptors are stored in `env.constrained`, so they are part of
        # the semantic environment — envs are compared for equality and frozen
        # into published module interfaces. `head_arg_type` and `return_type` are
        # slices of the signature's surface AST, and keeping their spans made an
        # interface depend on where in the file the function was written.
        # `Cure.Elab.Resolve.result_head_core/3` reads them structurally.
        {dparam,
         %{
           iface: iface_atom,
           tyvar: tyvar,
           head_arg_index: idx,
           head_arg_type: Metadata.strip_diagnostics(head_arg_type),
           return_type: Metadata.strip_diagnostics(return_expr),
           dict_name: dict_name
         }}
      end)
      |> Enum.unzip()

    {params ++ dict_params, specs}
  end

  defp type_ast_mentions_variable?({:variable, _meta, name}, name), do: true

  defp type_ast_mentions_variable?({_tag, _meta, children}, name) when is_list(children),
    do: Enum.any?(children, &type_ast_mentions_variable?(&1, name))

  defp type_ast_mentions_variable?(_ast, _name), do: false

  # Demote each dictionary parameter to `:erased` when the body would still pass
  # the relevance check with it erased — i.e. it is never used relevantly. This is
  # the exact soundness criterion `Relevance.check` enforces, so a demoted dict is
  # safe for erasure to drop. Non-dict quantities are never touched.
  defp demote_unused_dicts(env, %{params: params, quantities: quantities, name: name}, body) do
    dict_positions =
      params
      |> Enum.with_index()
      |> Enum.filter(fn {{:param, m, _n}, _i} -> Keyword.has_key?(m, :constraint_dict) end)
      |> Enum.map(fn {_p, i} -> i end)

    Enum.reduce(dict_positions, quantities, fn pos, qs ->
      trial = List.replace_at(qs, pos, :erased)

      case Relevance.check(env, name, trial, body) do
        :ok -> trial
        _ -> qs
      end
    end)
  end

  # A parameterized record `rec Box(a)\n  val: a` is a single-constructor
  # parameterized family. Build the constructor through the shared GADT-ctor
  # machinery from a NAMED-domain signature (`struct_ctor_sig`), which handles the
  # parameter telescope and the de-Bruijn-correct result parameters AND names the
  # ctor telescope by the fields (so construction/projection find them) while
  # threading each field into scope for the following field types (a dependent
  # record — `rec Box(a)\n  n: Nat\n  v: Vec(a, n)`).
  @doc """
  Declare a compiler-GENERATED, parameterless, index-free inductive family from
  pre-built Core constructor records. The public entry `Cure.Elab.Union` uses to
  realise an anonymous union (`Int | String`) as a real discriminated family.

  Goes through the same kernel gate as every surface declaration —
  `Kernel.check_family`, `check_all_ctors`, `Inductive.positive?` — so a generated
  family cannot bypass the TCB.
  """
  @spec declare_generated_family(Env.t(), atom(), [map()]) :: {:ok, Env.t()} | {:error, term()}
  def declare_generated_family(env, name, ctors) do
    # Anonymous unions derive their identity from their canonical member set,
    # so an enclosing module must not become part of the generated family or
    # constructor keys.  Keep the caller's owner on the returned environment;
    # only this compiler-generated registration is ownerless.
    generated_env = Env.with_owner(env, nil)

    case declare_indexed_at_min_level(generated_env, name, [], [], ctors, 0) do
      {:ok, result} -> {:ok, Env.with_owner(result, Env.owner(env))}
      {:error, _} = error -> error
    end
  end

  @doc """
  Declare a single-constructor record family `name(type_params)` whose fields are
  `[{:param, [type: ast], fname}]`. This is the public entry the typeclass
  elaborator uses to realise an interface as its dictionary record type former
  (`Eqs(a) ≙ Eqs{ eqs : a -> a -> Bool }`).
  """
  @spec declare_record(atom(), [String.t()], [tuple()], Env.t()) ::
          {:ok, Env.t()} | {:error, term()}
  def declare_record(name, type_params, fields, env) do
    # `interface` reaches family declaration through HERE, not through the container
    # clauses — so without this it bypassed the reserved-namespace guard entirely and a
    # backtick-named interface could overwrite a generated union family.
    with :ok <- reject_reserved_family_name(name) do
      declare_parameterized_struct(name, type_params, fields, env)
    end
  end

  defp declare_parameterized_struct(name, type_params, fields, env) do
    params = Enum.map(type_params, fn p -> {:param, [], p} end)
    sig = struct_ctor_sig(name, type_params, fields)

    with {:ok, param_tele} <- elaborate_index_telescope(params, name, env, [], :duplicate_parameter),
         working_env = Inductive.declare(env, Inductive.family(name, param_tele, [], 0), []),
         {:ok, [ctor]} <- elaborate_gadt_ctors([sig], name, param_tele, [], working_env) do
      declare_indexed_at_min_level(env, name, param_tele, [], [ctor], 0)
    end
  end

  # A record `rec R(params)\n f1: T1\n f2: T2` as a single GADT-constructor signature
  # with NAMED field domains, so `elaborate_gadt_ctor`'s named-binder scope-threading
  # binds each field for the following field types (a dependent record) and names the
  # resulting ctor telescope by the fields (what construction/projection read).
  defp struct_ctor_sig(name, type_params, fields) do
    named_doms =
      Enum.map(fields, fn {:param, m, fname} ->
        {:named_dom, [name: fname], [Keyword.fetch!(m, :type)]}
      end)

    {:gadt_ctor, [name: Atom.to_string(name)], [{:arrow_chain, [], named_doms ++ [family_app(name, type_params)]}]}
  end

  # A record field may declare a default (`name: String = "Anonymous"`), carried in
  # the field param's `:default` meta. Stash the defaults, keyed by field-name atom
  # (matching the ctor's `args` telescope labels), on the constructor map as
  # `:field_defaults` so `desugar_record_construction` can fill any field the caller
  # omits. Purely an E-layer annotation — a plain extra key on the ctor map that the
  # kernel never reads. A ctor with no defaulted field is left untouched.
  defp attach_field_defaults(ctor, fields) do
    case record_field_defaults(fields) do
      defaults when map_size(defaults) == 0 -> ctor
      defaults -> Map.put(ctor, :field_defaults, defaults)
    end
  end

  defp record_field_defaults(fields) do
    Enum.reduce(fields, %{}, fn
      {:param, m, fname}, acc ->
        case Keyword.get(m, :default) do
          nil -> acc
          expr -> Map.put(acc, String.to_atom(fname), expr)
        end

      _, acc ->
        acc
    end)
  end

  defp register_record_field_sites({:ok, declared}, owner_env, name, fields) do
    sites =
      Map.new(fields, fn {:param, meta, field_name} ->
        info = Cure.MetaAST.Metadata.source_info(meta)

        {field_name,
         %{
           span: info && info.whole,
           name_span: info && info.name,
           type_span: info && info.annotation
         }}
      end)

    :ok =
      Cure.Elab.SourceMetadata.put_record_field_sites(
        Env.owned_name(owner_env, name),
        sites
      )

    {:ok, declared}
  end

  defp register_record_field_sites(error, _owner_env, _name, _fields), do: error

  # A positional enum variant, seen as a GADT constructor signature that returns
  # the family applied to its own parameters. `Nil` → `Nil : List(a)`;
  # `Cons(a, List(a))` → `Cons : a -> List(a) -> List(a)`.
  defp variant_to_gadt_sig({:variable, _meta, vname}, fam, type_params) do
    {:gadt_ctor, [name: vname], [{:arrow_chain, [], [family_app(fam, type_params)]}]}
  end

  defp variant_to_gadt_sig({:function_def, cmeta, _body}, fam, type_params) do
    cname = Keyword.fetch!(cmeta, :name)
    field_asts = Keyword.fetch!(cmeta, :params)
    {:gadt_ctor, [name: cname], [{:arrow_chain, [], field_asts ++ [family_app(fam, type_params)]}]}
  end

  defp family_app(fam, type_params) do
    args = Enum.map(type_params, fn p -> {:variable, [scope: :local], p} end)
    {:function_call, [name: Atom.to_string(fam)], args}
  end

  # Declare a family with a parameter telescope and (optionally) an index
  # telescope from GADT-style constructor signatures. Shared by indexed types and
  # parameterized enums (the latter pass no indices).
  defp declare_parameterized(name, params, index_params, ctor_sigs, env) do
    with :ok <- reject_reserved_ctor_names(ctor_sigs) do
      do_declare_parameterized(name, params, index_params, ctor_sigs, env)
    end
  end

  defp do_declare_parameterized(name, params, index_params, ctor_sigs, env) do
    # Parameters are the outer binders: elaborate the param telescope first, then
    # the index telescope in the scope of the parameters (most-recent first).
    param_scope = params |> Enum.map(fn {:param, _m, n} -> n end) |> Enum.reverse()

    with {:ok, param_tele} <- elaborate_index_telescope(params, name, env, [], :duplicate_parameter),
         {:ok, index_tele} <- elaborate_index_telescope(index_params, name, env, param_scope),
         # Pre-register the family signature (empty ctors, tentative level) so
         # self-references in constructor signatures — e.g. `Vector(a, n)` as a
         # `prepend` domain — resolve their parameter arity via param_count when
         # converted to Core. The authoritative declaration happens below.
         working_env = Inductive.declare(env, Inductive.family(name, param_tele, index_tele, 0), []),
         {:ok, ctors} <- elaborate_gadt_ctors(ctor_sigs, name, param_tele, index_tele, working_env) do
      declare_indexed_at_min_level(env, name, param_tele, index_tele, ctors, 0)
    end
  end

  # -- function elaboration ---------------------------------------------------

  defp single_body([expr]), do: expr
  defp single_body(expr), do: expr

  # A `match` body needs the declared return type to build its motive (checking
  # mode); every other body is elaborated in inference mode.
  defp elaborate_body({:pattern_match, meta, [scrut | arms]} = expr, return_core, scope, ctx, env, _params) do
    if Elaborator.special_match_arms?(arms) do
      Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
    else
      result = Elaborator.elaborate_match(scrut, arms, return_core, scope, ctx, env)

      if Keyword.get(meta, :induction) do
        Induction.wrap_match_error(result, meta, arms)
      else
        result
      end
    end
  end

  # A `with <expr>` body (capability A): like `match`, but its motive
  # value-abstracts the scrutinee EXPRESSION out of the goal, so each branch's
  # goal is refined to the branch constructor's value (goal refinement plain
  # `match` cannot do). Checking mode — the declared return type is the goal.
  defp elaborate_body({:with_abs, meta, [scrut | arms]}, return_core, scope, ctx, env, params) do
    proof = Keyword.get(meta, :proof)
    Elaborator.elaborate_with(scrut, arms, proof, return_core, scope, ctx, env, params)
  end

  defp elaborate_body({:rewrite_expr, _meta, _children} = expr, return_core, scope, ctx, env, _params) do
    Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
  end

  defp elaborate_body({:function_call, meta, _args} = expr, return_core, scope, ctx, env, _params) do
    name = Keyword.get(meta, :name)
    atom = if is_binary(name), do: String.to_atom(name)

    cond do
      name == "reflexive" ->
        Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

      atom && Cure.Elab.Resolve.result_dispatched_method?(env, atom) ->
        # A method such as `BeamDecode.from_beam : BeamTerm -> Result(t, E)`
        # determines its interface head from the declared result, not an input.
        # Keep the body in checking mode so result-directed instance selection
        # receives that goal instead of classifying the BeamTerm argument.
        Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

      # A call whose declared return type mentions a generated anonymous-union family
      # must be CHECKED, not inferred. Inferring `Std.Map.put(:a, 1, …)` solves the
      # map's implicit `v := Int` from the first value argument, and only then compares
      # `Map(Atom, Int)` against the goal `Map(Atom, Int | Bool)` — which fails, since
      # there is no container covariance. Checking threads the goal into the
      # application, so `v` is solved from the GOAL and each value is injected instead.
      Elaborator.union_goal?(return_core) ->
        Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

      atom && Inductive.get_ctor(env, atom) ->
        # A constructor body is checked against the declared return type, so a
        # nullary or otherwise underdetermined constructor (`Nil()` at
        # `-> List(Nat)`) can pin its implicit parameters from the goal rather than
        # failing with unsolved metavariables under pure inference.
        Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

      Elaborator.refinement_return?(return_core, ctx, env) ->
        # A non-constructor call at a refinement return (`fn f(...) -> {n: T | φ} =
        # g(...)`). Route it through `elaborate_refinement_return_body/6`: a call
        # that already infers to a refinement value (`refine(v, pf)`) is a complete
        # term and is kept verbatim; only a call inferring to the base type
        # (`multiply(a, b)` at `{n | IsPositive(n)}`) is CHECKED so its obligation
        # reaches the proof-search discharge (`try_discharge_refinement`).
        elaborate_refinement_return_body(expr, return_core, scope, ctx, env, fn ->
          elaborate_call_body_infer(expr, return_core, scope, ctx, env)
        end)

      true ->
        elaborate_call_body_infer(expr, return_core, scope, ctx, env)
    end
  end

  # A pair `%[a, b]` is a dependent-pair introduction; the kernel checks it
  # against the declared Σ return type.
  defp elaborate_body({:tuple, _meta, elems} = expr, return_core, scope, ctx, env, _params)
       when is_list(elems) and length(elems) >= 2 do
    # Check the tuple against the declared return type first, so a *dependent* pair
    # (`Sigma(n: Nat, Vector(a, n))`) elaborates its second component against the
    # codomain instantiated at the first — otherwise a component like
    # `prepend(x, empty())` is inferred and its underdetermined parts are left as
    # unsolved metavariables. A flat telescope `Tuple(T1,…,Tn)` = `%[e1,…,en]`
    # likewise checks each element against its Σ layer (`check_tuple_against/5`).
    # For an arity-2 pair only, fall back to inferring both components when the
    # return type is not a Σ the checker can use (preserving the prior behaviour).
    case Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env) do
      {:ok, term} ->
        {:ok, term}

      {:error, _} = err ->
        case elems do
          [a_ast, b_ast] ->
            with {:ok, a_term, _} <- Elaborator.elaborate_expr_typed(a_ast, scope, ctx, env),
                 {:ok, b_term, _} <- Elaborator.elaborate_expr_typed(b_ast, scope, ctx, env) do
              {:ok, {:ctor, sigma_mk_pair(env), [a_term, b_term]}}
            end

          _ ->
            err
        end
    end
  end

  # A hole body `?name` elaborates to a `:hole` term (accepted at the declared
  # return type by the kernel; it blocks codegen until filled).
  defp elaborate_body({:hole, _meta, _} = expr, return_core, scope, ctx, env, _params) do
    # A whole-body proof hole is a check-position hole against the declared return
    # type: route it through the proof-hole trigger so `@lemma`-tagged theorems and
    # local hypotheses can auto-discharge it. Strictly additive — on `:none` the
    # trigger returns the same surviving `{:hole, id}` this clause used to build.
    Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
  end

  # A `let … ⏎ body` block: check it against the declared return type (there is
  # no `:let` in Core — the elaborator desugars each binding to a β-redex).
  defp elaborate_body({:block, _meta, _stmts} = expr, return_core, scope, ctx, env, _params) do
    Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
  end

  # `if …` as a function body: check it against the declared return type so both
  # branches inherit the expected type (a constant-motive `:case` on the inductive Bool).
  defp elaborate_body({:conditional, _meta, _} = expr, return_core, scope, ctx, env, _params) do
    Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
  end

  # A lambda body has untyped parameters, so it must be *checked* against the
  # declared return type (a Π) rather than inferred — `fn(y) -> …` returning a
  # function type. Other bodies stay on the inference path below.
  defp elaborate_body({:lambda, _meta, _} = expr, return_core, scope, ctx, env, _params) do
    Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
  end

  # A `[]`/`[h|t]`/`[a,b,c]` body: check it against the declared return type so a
  # bare `[]` (which desugars to `Nil` with a metavariable element type) pins that
  # element type from the goal instead of failing `{:unsolved_metavariables, :Nil}`
  # (Finding A). `elaborate_expr_checked` self-desugars the `:list` node.
  defp elaborate_body({:list, _, _} = expr, return_core, scope, ctx, env, _params),
    do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

  # A `pickup …` body: check it against the declared return type so a first clause
  # whose then-branch is bare `[]` (the `take` shape) pins its element type from
  # the goal rather than being elaborated infer-only first.
  defp elaborate_body({:pickup, _, _} = expr, return_core, scope, ctx, env, _params),
    do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

  # A bare literal body is checked against the declared return type so a numeric
  # literal at `Nat`/`Bounded(n)` lowers to its compact `{:nat_lit,_}`/
  # `{:bounded_lit,_}` form (`fn a() -> Char = 97`), instead of inferring `Int` and
  # then failing conversion. Non-numeric / Int/Float literals fall through the
  # checked path to the same infer-and-convert behavior as before.
  defp elaborate_body({:literal, _meta, _value} = expr, return_core, scope, ctx, env, _params),
    do: Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

  # A negative integer spelling parses as unary `-` over a positive literal.
  # Keep this whole-body form in checking mode so the declared result can select
  # `ExpressibleByIntegerLiteral`; inference would prematurely default the
  # operand and the negation to Int.
  defp elaborate_body(
         {:unary_op, meta, [{:literal, literal_meta, value}]} = expr,
         return_core,
         scope,
         ctx,
         env,
         _params
       )
       when is_integer(value) and value >= 0 do
    if Keyword.get(meta, :operator) == :- and Keyword.get(literal_meta, :subtype) == :integer do
      Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)
    else
      elaborate_body_infer(expr, return_core, scope, ctx, env)
    end
  end

  # The general body: elaborated in INFER mode. `coerce_union/5` is a strict no-op
  # unless the declared return type is a generated anonymous-union family — in which
  # case the inferred term is injected into the matching member constructor. Without
  # it, `fn f(n: Int) -> Int | Bool = n` never reaches check-position at all (this
  # clause discards `return_core`), so the injection would never fire and the kernel
  # would reject `Int` at the union type.
  defp elaborate_body(expr, return_core, scope, ctx, env, _params) do
    cond do
      # A union-goal body (e.g. a map literal at `Map(Atom, Int | Bool)`) is CHECKED,
      # so the goal reaches the application and its implicits are solved from the goal
      # rather than from the first value.
      Elaborator.union_goal?(return_core) ->
        Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env)

      # A refinement return `{x: T | φ}` is CHECKED so an OPEN obligation (one whose
      # truth depends on a binder, e.g. `{n: Int | n > 0}` for a body mentioning a
      # parameter) reaches `try_discharge_refinement` and can be discharged by proof
      # search — the infer path below discards `return_core` and so never reaches
      # check-position. Check mode is kernel-sound (every proposed proof is
      # re-checked), so this only ACCEPTS more, never wrongly; if it does not apply
      # (the body is not a value that discharges), fall back to the infer path, which
      # still coerces an already-refined body down to its base where needed.
      Elaborator.refinement_return?(return_core, ctx, env) ->
        elaborate_refinement_return_body(expr, return_core, scope, ctx, env, fn ->
          elaborate_body_infer(expr, return_core, scope, ctx, env)
        end)

      true ->
        elaborate_body_infer(expr, return_core, scope, ctx, env)
    end
  end

  # A body at a refinement return (`fn f(...) -> {x: T | φ} = body`). Infer the
  # body first: if it ALREADY has a refinement type (it constructed the pair
  # itself — `refine(v, pf)`, or is a variable of refinement type), it is a
  # complete term and is kept verbatim via `infer_fallback`, so its author-written
  # or proof-searched projection accessors are NOT re-derived by a redundant
  # checked pass (which picks a different-but-convertible projection head —
  # `Std.Sigma#sigma_first` where the direct term used `Std.Refine#refined_value`,
  # the ProofHole differential regression). Only a body inferring to a
  # NON-refinement base value (`multiply(a, b)` at `{n | IsPositive(n)}`) needs the
  # goal threaded in so its refinement obligation reaches `try_discharge_refinement`
  # — that is the CHECK pass. Every proposed proof is kernel-rechecked, so checking
  # only ever ACCEPTS more; on any failure, `infer_fallback` restores the exact
  # currently-accepted/-rejected behaviour.
  defp elaborate_refinement_return_body(expr, return_core, scope, ctx, env, infer_fallback) do
    case Elaborator.elaborate_expr_typed(expr, scope, ctx, env) do
      {:ok, _term, type} ->
        if Elaborator.inferred_refinement_value?(type, ctx, env) do
          infer_fallback.()
        else
          case Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env) do
            {:ok, checked} -> {:ok, checked}
            _ -> infer_fallback.()
          end
        end

      {:error, _} ->
        case Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env) do
          {:ok, checked} -> {:ok, checked}
          _ -> infer_fallback.()
        end
    end
  end

  # The historical infer-first body path. `coerce_union/5` is a strict no-op unless
  # the declared return type is a generated anonymous-union family (then the inferred
  # term is injected into the matching member constructor); `coerce_refined_to_base/5`
  # is a strict no-op unless the inferred type is a refinement Sigma and the return is
  # its base component (then the first projection is inserted).
  defp elaborate_body_infer(expr, return_core, scope, ctx, env) do
    with {:ok, term, type} <- Elaborator.elaborate_expr_typed(expr, scope, ctx, env) do
      term = Elaborator.coerce_union(term, type, return_core, ctx, env)
      {:ok, Elaborator.coerce_refined_to_base(term, type, return_core, ctx, env)}
    end
  end

  # A non-constructor call body is inferred, then (mirroring the constructor branch
  # in the `{:function_call, …}` clause of `elaborate_body/6`, and
  # `elaborate_branch_body`'s function-call arm) retried in *checking* mode when
  # inference fails only because it could not synthesise a standalone type. Two such
  # failures both want the goal threaded in:
  #
  #   * `:unsolved_metavariables` — an implicit determined by NEITHER argument, only
  #     by the declared return type (`mk(Z()) : Const(Nat, Bool)`, whose phantom `{b}`
  #     no argument fixes) — solved from the goal;
  #   * `:unsupported_expression` — an argument that cannot infer standalone, the
  #     load-bearing case being an unannotated lambda whose domain only the goal fixes
  #     (`mk(fn(x) -> x.1) : Box(Tuple(Int,Int), Int)`): checking against the goal
  #     solves the callee's implicit `s`/`a` first, giving the lambda a concrete
  #     (tuple) domain so its `.i` projection lowers.
  #
  # Additive: the checked retry runs only after inference already errored, and the
  # original error is surfaced if the retry also fails, so every currently-accepted or
  # -rejected body is unchanged.
  defp elaborate_call_body_infer(expr, return_core, scope, ctx, env) do
    case Elaborator.elaborate_expr_typed(expr, scope, ctx, env) do
      {:ok, term, type} ->
        # `coerce_union/5` is a strict no-op unless the declared return type is a
        # generated anonymous-union family. This branch discards `return_core`, so
        # without it a call body like `fn wide(n: Int) -> Int | Bool | Atom =
        # narrow(n)` would never be injected or widened.
        {:ok, Elaborator.coerce_union(term, type, return_core, ctx, env)}

      {:error, reason} = orig
      when is_tuple(reason) and
             elem(reason, 0) in [:unsolved_metavariables, :unsupported_expression] ->
        case Elaborator.elaborate_expr_checked(expr, return_core, scope, ctx, env) do
          {:ok, term} -> {:ok, term}
          {:error, _} -> orig
        end

      {:error, _} = orig ->
        orig
    end
  end

  # Deterministic hole identity (first-class holes, Slice 1). Every source `?`
  # must get a UNIQUE id: once holes flow through the kernel as stuck neutrals,
  # two holes sharing an id are definitionally equal, so `refl : ?a = ?b` would
  # type-check and a false equality be forgeable. A NAMED `?foo` keys on its name
  # so repeating `?foo` *within one def* refers to the SAME unknown; an unnamed
  # `?` keys on its source position (`line:col`), unique per occurrence. Both are
  # qualified by `<module>.<def>` (`Env.owner/1` + `Env.current_def/1`) — the
  # <def> qualifier is REQUIRED for the named case: without it, `?goal` written
  # in two different defs of the same module mints the SAME id, and `Conv`
  # (`conv_neutral?({:nhole,id},{:nhole,id}) -> true`) judges those two,
  # semantically-unrelated holes definitionally equal (cross-def collision — see
  # `Cure.Elab.HoleIdentityTest` "cross-def collision guard"). No gensym counter
  # is used, so Antigen and the differential oracle stay replay-stable.
  #
  # Public so the elaborator's proof-hole trigger (Elaborator.elaborate_expr_checked
  # for `{:hole,_}` in argument position) mints ids by the SAME scheme — one
  # source of hole identity, no drift.
  @doc false
  def hole_id(env, meta) do
    mod = Env.owner(env) || ""
    def_name = Env.current_def(env)
    qualifier = if def_name, do: "#{mod}.#{def_name}", else: mod
    name = Keyword.get(meta, :name, "")

    if name != "" do
      "#{qualifier}##{name}"
    else
      "#{qualifier}:#{Keyword.get(meta, :line, 0)}:#{Keyword.get(meta, :col, 0)}"
    end
  end

  # The registered Sigma constructor name (canonically `:mk_pair`), via the builtin
  # registry; defaults to `:mk_pair` when no Sigma family is registered.
  defp sigma_mk_pair(env) do
    with fam when not is_nil(fam) <- Inductive.builtin(env, :sigma),
         [%{name: n} | _] <- Inductive.ctors_of(env, fam) do
      n
    else
      _ -> :mk_pair
    end
  end

  # Convert the parameter list into a Core telescope + {0,ω} quantities, with each
  # parameter type elaborated in the scope of the preceding parameters. Implicit
  # (`{name}`) parameters are erased. Returns the scope (names, most-recent first).
  # Collect the signature's free type variables (lowercase, unbound, not a known
  # family) that occur in a kind-`Type` position, and return them as leading
  # implicit parameters in order of first appearance.
  defp auto_generalize(params, return_expr, env) do
    bound = params |> Enum.map(fn {:param, _m, n} -> n end) |> MapSet.new()

    type_asts =
      Enum.map(params, fn {:param, m, _n} -> Keyword.get(m, :type) end) ++ [return_expr]

    {ordered, _seen} =
      type_asts
      |> Enum.reject(&is_nil/1)
      |> Enum.reduce({[], MapSet.new()}, fn ast, acc -> collect_type_vars(ast, bound, env, acc) end)

    Enum.map(ordered, fn n -> {:param, [implicit: true], n} end)
  end

  # A type variable occurs here at kind `Type`: collect it if lowercase, unbound,
  # not `Type`, and not a known family.
  defp collect_type_vars({:variable, _m, name}, bound, env, {ordered, seen} = acc) do
    cond do
      not type_var_name?(name) -> acc
      name == "Type" -> acc
      MapSet.member?(bound, name) -> acc
      MapSet.member?(seen, name) -> acc
      Inductive.family?(env, String.to_atom(name)) -> acc
      true -> {ordered ++ [name], MapSet.put(seen, name)}
    end
  end

  # A function type `(A) -> B`: every domain and the codomain is a type (kind Type).
  # A family/type application `F(args)`: only the leading parameter slots whose kind
  # is `Type` are kind-`Type` positions; index slots (e.g. `Vec(a, n)`'s `n : Nat`)
  # are not, so they are skipped and their variables are left to normal resolution.
  defp collect_type_vars({:function_call, meta, args}, bound, env, acc) do
    if Keyword.get(meta, :function_type) do
      Enum.reduce(args, acc, &collect_type_vars(&1, bound, env, &2))
    else
      fam = String.to_atom(Keyword.get(meta, :name, ""))

      case Env.get_def(env, fam) do
        %{type: type, body: body} when is_tuple(body) ->
          if typealias_parameter_count(type) >= 0 do
            Enum.reduce(args, acc, &collect_type_vars(&1, bound, env, &2))
          else
            acc
          end

        _ ->
          {pc, ptele} =
            if Inductive.family?(env, fam),
              do: {Inductive.param_count(env, fam), Inductive.param_telescope(env, fam) || []},
              else: {0, []}

          args
          |> Enum.with_index()
          |> Enum.reduce(acc, fn {arg, i}, acc2 ->
            if i < pc and match?({:type, _}, elem(Enum.at(ptele, i, {nil, nil}), 1)),
              do: collect_type_vars(arg, bound, env, acc2),
              else: acc2
          end)
      end
    end
  end

  defp collect_type_vars({:sigma_type, _m, children}, bound, env, acc) when is_list(children) do
    Enum.reduce(children, acc, &collect_type_vars(&1, bound, env, &2))
  end

  defp collect_type_vars({:refinement_type, _m, children}, bound, env, acc) when is_list(children) do
    Enum.reduce(children, acc, &collect_type_vars(&1, bound, env, &2))
  end

  defp collect_type_vars({:tuple_type, _m, children}, bound, env, acc) when is_list(children) do
    Enum.reduce(children, acc, &collect_type_vars(&1, bound, env, &2))
  end

  defp collect_type_vars(_other, _bound, _env, acc), do: acc

  defp type_var_name?(<<c, _::binary>>) when c in ?a..?z, do: true
  defp type_var_name?(_), do: false

  # A record must not declare the same field name twice: fields become the named
  # constructor telescope (and records compile to BEAM maps keyed by field name), so
  # a duplicate silently collapses one field. Idris/Agda/Lean reject duplicate record
  # fields.
  defp check_no_duplicate_fields(fields) do
    names =
      Enum.flat_map(fields, fn
        {:param, _m, fname} -> [fname]
        _ -> []
      end)

    case names -- Enum.uniq(names) do
      [] -> :ok
      [dup | _] -> {:error, {:duplicate_field, duplicate_binder_details(fields, dup)}}
    end
  end

  # The first repeated (non-wildcard) binder name in a `{:param, _, name}` list,
  # or nil if the telescope is linear. Shared by every telescope builder — a
  # repeated binder makes later types / bodies that reference it ambiguous.
  defp duplicate_param_name(params) do
    names =
      params
      |> Enum.flat_map(fn
        {:param, _m, n} -> [n]
        _ -> []
      end)
      |> Enum.reject(&(&1 == "_"))

    case names -- Enum.uniq(names) do
      [] -> nil
      [dup | _] -> dup
    end
  end

  defp elaborate_param_telescope(params, env) do
    # A telescope must not bind the same parameter name twice: a later parameter's
    # type (and the body) can refer to an earlier binder by name, so a duplicate
    # silently shadows the first and makes the reference ambiguous. Idris/Agda/Lean
    # reject repeated binder names in a telescope.
    # The bare wildcard `_` binds nothing, so it is exempt — several ignored
    # arguments may all be `_`.
    pnames =
      params
      |> Enum.map(fn {:param, _m, n} -> n end)
      |> Enum.reject(&(&1 == "_"))

    case pnames -- Enum.uniq(pnames) do
      [dup | _] ->
        {:error, {:duplicate_parameter, duplicate_binder_details(params, dup)}}

      [] ->
        elaborate_param_telescope_rec(params, env)
    end
  end

  defp duplicate_binder_details(params, duplicate) do
    spans =
      params
      |> Enum.filter(fn {:param, _meta, name} -> name == duplicate end)
      |> Enum.map(fn {:param, meta, _name} ->
        case Cure.MetaAST.Metadata.source_info(meta) do
          %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
          _ -> nil
        end
      end)
      |> Enum.reject(&is_nil/1)

    %{name: String.to_atom(duplicate), spans: spans}
  end

  # The telescope-aligned external-label vector for a signature's parameters
  # (Ph2 argument labels). One entry per binder, in the same order as the
  # telescope/quantities: a per-parameter label descriptor giving the name the
  # caller may write and whether writing it is required.
  #
  #   `fn f(to dest: T)` — two-name → `{:required, "to"}` (external label `to`
  #     mandatory; the internal `dest` is private to the body).
  #   `fn f(x: T)`       — single-name → `{:optional, "x"}` (the caller may write
  #     `f(x: v)` or `f(v)`; the writable name IS the binder name).
  #
  # Auto-generalized implicits and injected dictionaries — which the surface never
  # labels — are `{:optional, <synthetic name>}`; being erased (implicits) or
  # unwritten (dicts) they never reach a written-label check. The internal name of
  # a single-name binder is RETAINED (not collapsed to `nil`) so a written optional
  # label can be validated against it — a label naming no parameter is an error
  # (spec §4). Optional labels never affect overload distinguishability, only
  # mandatory ones do (see `member_labels/2`). A no-parameter def stores no vector.
  defp param_label_vector([]), do: nil

  defp param_label_vector(params) do
    Enum.map(params, fn {:param, pm, n} ->
      case Keyword.get(pm, :label) do
        nil -> {:optional, param_name_string(n)}
        label -> {:required, to_string(label)}
      end
    end)
  end

  defp param_label_span_vector([]), do: nil

  defp param_label_span_vector(params) do
    Enum.map(params, fn {:param, meta, _name} ->
      case Cure.MetaAST.Metadata.source_info(meta) do
        %Cure.MetaAST.SourceInfo{name: %Cure.Diagnostic.Span{} = span} -> span
        %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
        _ -> nil
      end
    end)
  end

  defp register_parameter_spans(env, name, params) do
    owned_name = Env.owned_name(env, name)
    :ok = Cure.Elab.SourceMetadata.put_parameter_spans(owned_name, param_label_span_vector(params) || [])
    :ok = Cure.Elab.SourceMetadata.put_parameter_sites(owned_name, parameter_site_vector(params))
    env
  end

  defp parameter_site_vector(params) do
    Enum.map(params, fn {:param, meta, name} ->
      info = Cure.MetaAST.Metadata.source_info(meta)

      %{
        name: param_name_string(name),
        span: info && info.whole,
        name_span: info && info.name,
        type_span: info && info.annotation
      }
    end)
  end

  defp register_declaration_span(env, name, meta) do
    span =
      case Cure.MetaAST.Metadata.source_info(meta) do
        %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
        _source_info -> nil
      end

    :ok = Cure.Elab.SourceMetadata.put_declaration_span(Env.owned_name(env, name), span)
    env
  end

  defp param_name_string(n) when is_binary(n), do: n
  defp param_name_string(n) when is_atom(n), do: to_string(n)
  defp param_name_string(_), do: nil

  # The quantity a parameter binds at: an explicit surface grade wins, else the
  # position's default (`:erased` for an implicit, `ω` for an explicit).
  defp param_quantity(pmeta) do
    case Keyword.get(pmeta, :grade) do
      nil -> if Keyword.get(pmeta, :implicit), do: Grade.zero(), else: Grade.unrestricted()
      g -> g
    end
  end

  defp elaborate_param_telescope_rec(params, env) do
    params
    |> Enum.reduce_while({:ok, [], [], []}, fn {:param, pmeta, pname}, {:ok, tele, quants, scope} ->
      case Keyword.get(pmeta, :type) do
        nil ->
          if Keyword.get(pmeta, :implicit) do
            # A bare implicit parameter `{a}` (no kind) is a type variable ranging
            # over `Type`; it is erased, exactly like `{a: Type}`.
            {:cont, {:ok, tele ++ [{String.to_atom(pname), {:type, 0}}], quants ++ [:erased], [pname | scope]}}
          else
            info = Cure.MetaAST.Metadata.source_info(pmeta)

            {:halt,
             {:error,
              {:untyped_parameter,
               %{
                 name: pname,
                 span: info && (info.name || info.whole),
                 parameter_span: info && info.whole
               }}}}
          end

        type_expr ->
          # Parameter annotations are lowered in the context of the preceding
          # telescope, just like return annotations are lowered in the complete
          # parameter context. Passing `nil` here disabled the term-level
          # implicit-application path, so a call with an erased parameter inside
          # a dependent parameter type was emitted as a bare explicit-argument
          # spine. A middle implicit then shifted every following argument.
          ctx = build_context(env, tele)

          case idx_to_core(type_expr, scope, nil, env, ctx) do
            {:ok, core} ->
              # A surface grade (`c :linear T`, plan slice 5) overrides the position's
              # default: an implicit defaults to `:erased`, an explicit to `ω`. `ω`
              # itself has no spelling — it is written by omitting the grade — so each
              # grade has exactly one surface form.
              q = param_quantity(pmeta)
              {:cont, {:ok, tele ++ [{String.to_atom(pname), core}], quants ++ [q], [pname | scope]}}

            {:error, _} = err ->
              {:halt, err}
          end
      end
    end)
    |> case do
      {:ok, tele, quants, scope} -> {:ok, tele, quants, scope}
      {:error, _} = err -> err
    end
  end

  defp build_context(env, telescope, quantities \\ nil) do
    grades = binder_grades(quantities, length(telescope))

    telescope
    |> Enum.zip(grades)
    |> Enum.reduce(Context.empty(env), fn {{_name, type_core}, grade}, ctx ->
      # Weak-head-normalise each binder type so a type alias (`type Endo = (Nat) ->
      # Nat`, a certified δ-def) is stored as the underlying Π/Σ/data value the
      # kernel inspects — e.g. applying an `Endo`-typed parameter reaches a Π. This
      # is conversion-preserving (the alias is definitionally its right-hand side)
      # and idempotent for a type already in head form.
      type_value =
        type_core
        |> Eval.eval(Context.env(ctx))
        |> Cure.Core.Normalise.whnf_value(env)

      Context.extend(ctx, type_value, grade)
    end)
  end

  # Builds a `:pi`/`:lam` chain from a telescope, each binder carrying the grade at
  # its position in `quantities` (slice 6 — the Pi is the single source of truth). A
  # `nil` vector, or one shorter than the telescope, defaults the remainder to `ω`.
  # The binder tuple is assembled from a TAG, so no textual pass can see it — the
  # grade must be threaded here explicitly; `Term.term?/1` caught this during the
  # reshape.
  defp wrap_binders(tag, telescope, quantities, inner) do
    grades = binder_grades(quantities, length(telescope))

    telescope
    |> Enum.zip(grades)
    |> Enum.reverse()
    |> Enum.reduce(inner, fn {{_name, type}, g}, acc -> {tag, g, type, acc} end)
  end

  # Slice-6 guard: the stored Π and λ must carry the same grade at every binder
  # position. Both are built from one `quantities` vector by `wrap_binders/4`, so on
  # correct code this always holds; it fires only if a future change sources the two
  # from different vectors (mutation-validated: build the final Pi from the ORIGINAL
  # instead of the demoted vector → `{:grade_mismatch, %{pi:, lam:}}`). Structural,
  # so it never inspects a binder's TYPE — no whnf, no body re-check.
  defp assert_binder_grades_agree(pi, lam, name) do
    case grade_spine_mismatch(pi, lam) do
      nil -> :ok
      {pg, lg} -> {:error, {:grade_mismatch, %{def: name, pi: pg, lam: lg}}}
    end
  end

  defp grade_spine_mismatch({:pi, pg, _pd, pc}, {:lam, lg, _ld, lb}) do
    if pg == lg, do: grade_spine_mismatch(pc, lb), else: {pg, lg}
  end

  # Spines exhausted in lockstep (both built from the same telescope) — agreed.
  defp grade_spine_mismatch(_pi_cod, _lam_body), do: nil

  # §5.3: reject an `:erased` binder whose domain is `Effect`-headed — erasure
  # would delete a computation the type says must run. Walks the Pi spine like
  # `grade_spine_mismatch`; a non-Pi tail (the return type) ends the walk.
  defp assert_no_erased_effect_binder(pi, name), do: assert_no_erased_effect_binder(pi, name, 0)

  defp assert_no_erased_effect_binder({:pi, g, dom, cod}, name, index) do
    if Grade.erased?(g) and effect_headed?(dom),
      do: {:error, {:effect_binder_erased, %{def: name, binder: index}}},
      else: assert_no_erased_effect_binder(cod, name, index + 1)
  end

  defp assert_no_erased_effect_binder(_non_pi, _name, _index), do: :ok

  defp effect_headed?({:effect_type, _}), do: true
  defp effect_headed?(_), do: false

  defp binder_grades(nil, n), do: List.duplicate(Cure.Core.Grade.unrestricted(), n)

  defp binder_grades(quantities, n) do
    pad = n - length(quantities)
    if pad > 0, do: quantities ++ List.duplicate(Cure.Core.Grade.unrestricted(), pad), else: Enum.take(quantities, n)
  end

  # -- indexed families -------------------------------------------------------

  # The family's index telescope, converting each `i: T` in the scope of the
  # preceding index binders (most-recently-bound first).
  # `dup_tag` names the binder kind for the linearity error — this builder is shared
  # by the family PARAMETER telescope (`:duplicate_parameter`) and the INDEX
  # telescope (`:duplicate_index`).
  defp elaborate_index_telescope(params, fam, env, init_scope, dup_tag \\ :duplicate_index) do
    case duplicate_param_name(params) do
      nil -> elaborate_index_telescope_rec(params, fam, env, init_scope)
      dup -> {:error, {dup_tag, String.to_atom(dup)}}
    end
  end

  defp elaborate_index_telescope_rec(params, fam, env, init_scope) do
    params
    |> Enum.reduce_while({:ok, [], init_scope}, fn {:param, pmeta, pname}, {:ok, tele, scope} ->
      # A bare type parameter (`type Box(a)` → `{:param, [], "a"}`) carries no
      # explicit kind; it ranges over types, so default its kind to `Type`.
      type_ast = Keyword.get(pmeta, :type, {:variable, [scope: :local], "Type"})

      case idx_to_core(type_ast, scope, fam, env) do
        {:ok, core} ->
          {:cont, {:ok, tele ++ [{String.to_atom(pname), core}], [pname | scope]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, tele, _scope} -> {:ok, tele}
      {:error, _} = err -> err
    end
  end

  defp elaborate_gadt_ctors(sigs, fam, param_tele, index_tele, env) do
    Enum.reduce_while(sigs, {:ok, []}, fn sig, {:ok, acc} ->
      case elaborate_gadt_ctor(sig, fam, param_tele, index_tele, env) do
        {:ok, ctor} -> {:cont, {:ok, acc ++ [ctor]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp elaborate_gadt_ctor({:gadt_ctor, cmeta, [{:arrow_chain, _chain_meta, atoms}]}, fam, param_tele, index_tele, env) do
    cname = cmeta |> Keyword.fetch!(:name) |> String.to_atom()
    {dom_exprs, result_expr} = split_last(atoms)

    # The family's parameters are bound OUTSIDE this constructor's telescope (the
    # kernel binds them first, then the ctor args). Referencing a parameter from
    # a ctor arg type or the result therefore reaches past all ctor args into the
    # param region — model that by appending the params (most-recent first, so
    # they occupy the highest de Bruijn levels) to every local scope.
    param_count = length(param_tele)
    param_scope = param_tele |> Enum.map(fn {n, _t} -> Atom.to_string(n) end) |> Enum.reverse()

    with :ok <- ensure_linear_named_doms(dom_exprs),
         {:ok, applied_exprs} <-
           family_index_args(result_expr, fam)
           |> attach_constructor_result_context(
             cmeta,
             result_expr,
             fam,
             cname,
             length(param_tele),
             length(index_tele)
           ) do
      # Implicit index variables are inferred from every family application in
      # the signature (domains + the result), positionally typed by the family's
      # index telescope. Ordered by first appearance → the leading telescope.
      # Parameters are NOT inference candidates (see infer_implicits' skip).
      # Names bound by a NAMED dependent domain `(k: Nat)` or a RELEVANT IMPLICIT
      # domain `{k: Nat}`. Such a binder is a source-position argument, not an
      # inferred index variable, so it must be excluded from implicit inference
      # even though it appears in later domain types / the result index
      # (`SNat(k)`, `NVv(S(k))`). The two differ only in plicity: `(k: T)` is
      # explicit (positional), `{k: T}` is implicit (solved/named) — both retain
      # quantity ω. See `2026-07-18-relevant-implicit-ctor-index-design.md`.
      bound_names =
        for dom <- dom_exprs, name = bound_dom_name(dom), name != nil, into: MapSet.new(), do: name

      parameter_names = MapSet.new(param_scope)

      infer_exprs = Enum.map(dom_exprs, &strip_named_dom/1) ++ [result_expr]

      implicits =
        infer_exprs
        |> infer_implicits(fam, index_tele, env, param_count, param_scope)
        |> Enum.reject(fn {n, _t} ->
          MapSet.member?(bound_names, n) or MapSet.member?(parameter_names, n)
        end)

      impl_names = Enum.map(implicits, &elem(&1, 0))

      # Each inferred binder pushes the family's parameters one slot farther
      # out. `infer_implicits/6` returns types in the bare parameter frame, so
      # lift them over the preceding inferred binders before either the explicit
      # domains or result indices are elaborated.
      impl_tele =
        implicits
        |> Enum.with_index()
        |> Enum.map(fn {{n, ty}, i} -> {String.to_atom(n), Term.shift(ty, i, 0)} end)

      case build_explicit_tele(dom_exprs, impl_names, impl_tele, param_scope, param_tele, fam, env) do
        {:ok, expl_tele, expl_names, expl_plicities, expl_quantities} ->
          full_scope = Enum.reverse(impl_names ++ expl_names) ++ param_scope
          {param_exprs, index_exprs} = Enum.split(applied_exprs, param_count)

          # Result indices are full term expressions, not merely syntax trees.
          # Give their lowering the constructor telescope's real typing context
          # so an implicit global application nested in an index can solve its
          # hidden arguments (`step_evidence_thread(...)` inside an intrinsic
          # accepting-path index). Without this context `idx_to_core` emitted an
          # explicit-only application spine and interface registration leaked
          # `:arg_arity`.
          result_ctx = build_context(env, param_tele ++ impl_tele ++ expl_tele)

          with {:ok, result_params} <- map_idx_to_core(param_exprs, full_scope, fam, env, result_ctx),
               {:ok, result_indices} <-
                 lower_constructor_result_indices(
                   index_exprs,
                   result_params,
                   index_tele,
                   full_scope,
                   fam,
                   env,
                   result_ctx
                 ) do
            # Inferred index variables are erased (quantity 0); every
            # source-position domain — explicit `(k:T)` OR relevant implicit
            # `{k:T}` — is runtime-relevant (quantity ω). See M8.3 / M9.
            quantities =
              List.duplicate(:erased, length(impl_tele)) ++
                expl_quantities

            # Plicity decouples from quantity: inferred indices AND relevant
            # implicits `{k:T}` are :implicit (non-positional); explicit doms are
            # :explicit (positional). Application and pattern binding key off
            # plicity, erasure keys off quantity.
            plicities =
              List.duplicate(:implicit, length(impl_tele)) ++ expl_plicities

            {:ok,
             Inductive.ctor(
               cname,
               impl_tele ++ expl_tele,
               result_indices,
               quantities,
               result_params,
               plicities
             )}
          end

        {:error, _} = err ->
          err
      end
    end
  end

  # Constructor result indices are checking positions, not inference positions.
  # Lower every surface index left-to-right against the instantiated family
  # telescope. This is the single construction site for compact Bounded literals,
  # omitted constructor implicits, and nested constructor values: lowering an
  # entire index without its expected domain loses the field expectations needed
  # by values such as `Cons(Frame(Nil(), Nil()), Nil())`.
  defp lower_constructor_result_indices(
         expressions,
         result_params,
         index_tele,
         scope,
         fam,
         env,
         ctx
       ) do
    expressions
    |> Enum.zip(index_tele)
    |> Enum.reduce_while({:ok, []}, fn {expression, {_name, index_type}}, {:ok, checked} ->
      actuals = result_params ++ checked
      expected = Subst.instantiate(index_type, actuals)

      case idx_to_core_expected(expression, expected, scope, fam, env, ctx) do
        {:ok, checked_index} -> {:cont, {:ok, checked ++ [checked_index]}}
        {:error, _} = error -> {:halt, error}
      end
    end)
  end

  defp attach_constructor_result_context(
         {:error, {:result_type_not_family, _family} = reason},
         constructor_meta,
         result_expr,
         family,
         constructor,
         parameter_count,
         index_count
       ) do
    constructor_info = Cure.MetaAST.Metadata.source_info(constructor_meta)

    {:error,
     {:source_context, reason,
      %{
        span: surface_ast_span(result_expr),
        result_span: surface_ast_span(result_expr),
        constructor_span: constructor_info && constructor_info.whole,
        constructor_name_span: constructor_info && constructor_info.name,
        signature_span: constructor_info && constructor_info.annotation,
        expected_family: family,
        observed_family: constructor_result_head(result_expr),
        constructor: constructor,
        parameter_count: parameter_count,
        index_count: index_count
      }}}
  end

  defp attach_constructor_result_context(result, _meta, _expr, _family, _constructor, _params, _indices),
    do: result

  defp constructor_result_head({:function_call, meta, _arguments}), do: Keyword.get(meta, :name)
  defp constructor_result_head({:variable, _meta, name}), do: name
  defp constructor_result_head({tag, _meta, _children}) when is_atom(tag), do: tag
  defp constructor_result_head(_other), do: :unknown

  defp surface_ast_span({_tag, meta, _children}) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: span} -> span
      _ -> nil
    end
  end

  defp surface_ast_span(_other), do: nil

  defp split_last(list), do: {Enum.slice(list, 0..-2//1), List.last(list)}

  # For implicit-variable inference we scan a named `(k: Nat)` or relevant-
  # implicit `{k: Nat}` binder by its inner type (`Nat`); the binder name itself
  # is handled as a source-position arg, not an inferred index.
  defp strip_named_dom({:named_dom, _meta, [inner]}), do: inner
  defp strip_named_dom({:implicit_dom, _meta, [inner]}), do: inner
  defp strip_named_dom(other), do: other

  # The name a domain binds into the constructor's local scope, or `nil` for an
  # anonymous positional argument. Both `(k: T)` and `{k: T}` bind `k`.
  defp bound_dom_name({:named_dom, meta, _children}), do: Keyword.get(meta, :name)
  defp bound_dom_name({:implicit_dom, meta, _children}), do: Keyword.get(meta, :name)
  defp bound_dom_name(_other), do: nil

  # A constructor's named/implicit dependent domains must be linear: a repeated
  # binder (`(x: Nat) -> (x: Nat) -> …`) shadows and makes later references
  # ambiguous, exactly like a duplicate function parameter. `_` binds nothing.
  defp ensure_linear_named_doms(dom_exprs) do
    named = for dom <- dom_exprs, n = bound_dom_name(dom), n != nil, n != "_", do: n

    case named -- Enum.uniq(named) do
      [] -> :ok
      [dup | _] -> {:error, {:duplicate_parameter, String.to_atom(dup)}}
    end
  end

  defp family_index_args({:function_call, fmeta, args}, fam) do
    if String.to_atom(Keyword.fetch!(fmeta, :name)) == fam,
      do: {:ok, args},
      else: {:error, {:result_type_not_family, fam}}
  end

  defp family_index_args({:variable, _, name}, fam) do
    if String.to_atom(name) == fam,
      do: {:ok, []},
      else: {:error, {:result_type_not_family, fam}}
  end

  defp family_index_args(other, fam),
    do: {:error, {:bad_result_type, index_problem_details(other, family: fam)}}

  # Source-position telescope: convert each domain in the scope of all preceding
  # binders (inferred implicits, then earlier source-position doms). Returns the
  # telescope, the bound names, and the per-slot plicity — a NAMED `(k:T)` binder
  # is `:explicit` (positional), a RELEVANT IMPLICIT `{k:T}` binder is
  # `:implicit` (solved/named), an anonymous arg is `:explicit`.
  defp build_explicit_tele(dom_exprs, impl_names, impl_tele, param_scope, param_tele, fam, env) do
    dom_exprs
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, [], Enum.reverse(impl_names) ++ param_scope, [], [], []}, fn {dom, i},
                                                                                            {:ok, tele, scope, names,
                                                                                             plics, quantities} ->
      # A NAMED / IMPLICIT dependent binder uses its declared name (so later
      # domains and the result index can reference it); an unnamed arg keeps its
      # anonymous `_aN` name byte-for-byte. Either way the scope is threaded so
      # the next domain's de Bruijn indices resolve this binder.
      {argname, type_expr, plicity, quantity} =
        case dom do
          {:named_dom, meta, [inner]} ->
            {Keyword.fetch!(meta, :name), inner, :explicit, Keyword.get(meta, :grade, :unrestricted)}

          {:implicit_dom, meta, [inner]} ->
            {Keyword.fetch!(meta, :name), inner, :implicit, :unrestricted}

          _ ->
            {"_a#{i}", dom, :explicit, :unrestricted}
        end

      # Every constructor domain is checked in the typed telescope formed by
      # the family parameters, inferred indices, and preceding source fields.
      # Besides validating ordinary dependent references, this lets the shared
      # application elaborator insert a global function's hidden arguments from
      # an explicit later argument. Syntax-only lowering cannot do that: it
      # would turn `f(value)` into `f(value)` even when Core's telescope is
      # `{index} -> value -> ...`, shifting `value` into the hidden slot.
      ctx = build_context(env, param_tele ++ impl_tele ++ tele)

      case idx_to_core(type_expr, scope, fam, env, ctx) do
        {:ok, core} ->
          {:cont,
           {:ok, tele ++ [{String.to_atom(argname), core}], [argname | scope], names ++ [argname], plics ++ [plicity],
            quantities ++ [quantity]}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, tele, _scope, names, plics, quantities} -> {:ok, tele, names, plics, quantities}
      {:error, _} = err -> err
    end
  end

  # -- implicit index-variable inference --------------------------------------

  defp infer_implicits(exprs, fam, index_tele, env, self_param_count, param_scope) do
    {ordered, _seen} =
      Enum.reduce(exprs, {[], MapSet.new()}, fn e, acc ->
        collect_implicit_vars(e, fam, index_tele, env, self_param_count, param_scope, acc)
      end)

    ordered
  end

  # A function-type node `T1 -> … -> R` (a method's field type in a typeclass
  # dictionary record) carries `function_type: true` and NO `:name`. Recurse into
  # its arrow components so a head/index variable buried inside is still collected,
  # never treating it as a family application.
  defp collect_implicit_vars(
         {:function_call, fmeta, args},
         fam,
         index_tele,
         env,
         self_param_count,
         param_scope,
         acc
       )
       when is_list(fmeta) do
    if Keyword.get(fmeta, :function_type) do
      Enum.reduce(args, acc, fn a, ac ->
        collect_implicit_vars(a, fam, index_tele, env, self_param_count, param_scope, ac)
      end)
    else
      collect_named_call_implicits(
        {:function_call, fmeta, args},
        fam,
        index_tele,
        env,
        self_param_count,
        param_scope,
        acc
      )
    end
  end

  defp collect_implicit_vars(_other, _fam, _index_tele, _env, _self_param_count, _param_scope, acc), do: acc

  defp collect_named_call_implicits(
         {:function_call, fmeta, args},
         fam,
         index_tele,
         env,
         self_param_count,
         param_scope,
         acc
       ) do
    name = String.to_atom(Keyword.fetch!(fmeta, :name))
    index_types = family_index_types(name, args, fam, index_tele, env, param_scope)

    # A family application's leading `param_count` arguments are parameters, not
    # index-typed positions — skip them so the remaining args align 0-based with
    # the index telescope (and parameters are never collected as implicits).
    app_param_count =
      cond do
        name == fam -> self_param_count
        Inductive.family?(env, name) -> Inductive.param_count(env, name)
        true -> 0
      end

    acc =
      cond do
        index_types ->
          args
          |> Enum.drop(app_param_count)
          |> Enum.with_index()
          |> Enum.reduce(acc, fn {arg, pos}, a ->
            collect_index_expr_vars(a, arg, Enum.at(index_types, pos), fam, env)
          end)

        # A COMPUTED index expression: a non-family global function (`app`,
        # `dmeet`, `∧`, …) used inside an index. An index variable that appears
        # ONLY here (e.g. the fed-back `cv` in `app(av, cv)` inside a `loop`
        # constructor's ARGUMENT type) must still be inferred as an implicit,
        # typed by the function's domain telescope. Non-dependent domains only
        # (our index functions are non-dependent); a mistyped binder would fail
        # the kernel check, never silently mis-accept.
        dom = global_domain_types(name, env) ->
          args
          |> Enum.with_index()
          |> Enum.reduce(acc, fn {arg, pos}, a ->
            case arg do
              {:variable, _, vname} -> maybe_add_implicit(a, vname, Enum.at(dom, pos), fam, env)
              _ -> a
            end
          end)

        true ->
          acc
      end

    Enum.reduce(args, acc, fn a, ac ->
      collect_implicit_vars(a, fam, index_tele, env, self_param_count, param_scope, ac)
    end)
  end

  # Collect free variables from an index EXPRESSION typed by `type`, recursing into
  # constructor applications so a variable that appears only *inside* a constructor
  # in the result index — `m` in `fz : Fin(S(m))` / `FZ : Fin (S n)` — is inferred
  # as an implicit, typed by the enclosing constructor's field type. Idris binds
  # these automatically; without it the variable is unbound (`:index_mismatch`). A
  # bare variable is added directly (the pre-existing behaviour).
  defp collect_index_expr_vars(acc, {:variable, _, vname}, type, fam, env),
    do: maybe_add_implicit(acc, vname, type, fam, env)

  defp collect_index_expr_vars(acc, {:function_call, cmeta, cargs}, expected_type, fam, env) do
    cname = cmeta |> Keyword.fetch!(:name) |> String.to_atom()

    case Inductive.get_ctor(env, cname) do
      %{args: fields} = ctor ->
        # A surface constructor call contains only its positional (explicit)
        # arguments. Its full Core telescope also contains inferred/relevant
        # implicit slots. Aligning written args directly with `fields` assigned
        # the first payload to the leading erased type index (`Cons(left, xs)`
        # inferred `left : Type` instead of `left : a`), and computed result
        # indices later escaped as out-of-frame de Bruijn variables. Mirror the
        # ordinary constructor applicator: skip every implicit slot here.
        plicities = Map.get(ctor, :plicities) || List.duplicate(:explicit, length(fields))

        expected_params = expected_ctor_params(expected_type, ctor, env)
        field_types = written_ctor_field_types(fields, plicities, expected_params)

        cargs
        |> Enum.with_index()
        |> Enum.reduce(acc, fn {carg, i}, a ->
          collect_index_expr_vars(a, carg, Enum.at(field_types, i), fam, env)
        end)

      _ ->
        acc
    end
  end

  defp collect_index_expr_vars(acc, _other, _type, _fam, _env), do: acc

  # Parameters known from the enclosing expected family application specialize
  # a constructor's omitted leading implicit slots. For `Cons(left, rest)` under
  # expected `List(Int)`, this supplies `a := Int` before reading the written
  # head field's internal type `a`.
  defp expected_ctor_params({:data, dname, params, _indices}, ctor, env) do
    if Inductive.ctor_family(env, ctor.name) == dname, do: params, else: []
  end

  defp expected_ctor_params(_other, _ctor, _env), do: []

  defp written_ctor_field_types(fields, plicities, expected_params) do
    {types, _chosen} =
      Enum.zip(fields, plicities)
      # Constructor field types live in `family params ++ earlier ctor args`.
      # Seed substitution with the known family parameters; they are outside
      # `ctor.args` and therefore have no plicity slot of their own.
      |> Enum.reduce({[], expected_params}, fn {{_name, field_type}, plicity}, {types, chosen} ->
        specialized = Subst.instantiate(field_type, chosen)

        case plicity do
          :implicit ->
            {types, chosen ++ [{:hole, "__ctor_index_inference__"}]}

          :explicit ->
            # The written value itself is irrelevant to this field's type. Keep
            # a placeholder in the telescope substitution for any later field;
            # if a later type genuinely depends on it, its own occurrence will
            # still be checked by the constructor elaborator proper.
            {types ++ [specialized], chosen ++ [{:hole, "__ctor_payload_inference__"}]}
        end
      end)

    types
  end

  # Domain (argument) types of a defined global function, peeled from its Pi
  # type, or nil if `name` is not a defined global. Used to type index variables
  # occurring inside a computed index expression (see `collect_implicit_vars`).
  defp global_domain_types(name, env) do
    case Env.get_def(env, name) do
      %{type: ty} -> pi_domains(ty)
      _ -> nil
    end
  end

  defp pi_domains({:pi, _g, dom, cod}), do: [dom | pi_domains(cod)]
  defp pi_domains(_), do: []

  # The positional index types of family `name` (self or already registered).
  defp family_index_types(name, args, fam, index_tele, env, param_scope) do
    {param_count, tele} =
      cond do
        name == fam -> {length(args) - length(index_tele), index_tele}
        Inductive.family?(env, name) -> {Inductive.param_count(env, name), Inductive.index_telescope(env, name) || []}
        true -> {0, nil}
      end

    with tele when is_list(tele) <- tele,
         {:ok, actuals} <- map_idx_to_core(Enum.take(args, param_count + length(tele)), param_scope, fam, env) do
      tele
      |> Enum.with_index()
      |> Enum.map(fn {{_binder, type}, index_position} ->
        # An index telescope entry is scoped over the family parameters and all
        # earlier indices. Instantiate that prefix with the actual application
        # arguments, yielding a type in the surrounding constructor-parameter
        # frame. This is the crucial difference between `Consumed(t, …)` and
        # blindly copying `Consumed`'s internal `a` slot.
        Subst.instantiate(type, Enum.take(actuals, param_count + index_position))
      end)
    else
      _ -> nil
    end
  end

  defp maybe_add_implicit({ordered, seen} = acc, vname, type, fam, env) do
    atom = String.to_atom(vname)

    cond do
      type == nil ->
        acc

      # The indexed-type surface parser historically represents a numeral in
      # an index expression as `{:variable, ..., "1"}`; `idx_to_core` later
      # lowers that spelling to a compact literal. It is never an inferable
      # identifier. Binding it here manufactures a hidden constructor argument
      # named `:"1"` which cannot occur in the result after literal lowering,
      # so even a nullary exact-view constructor remains spuriously unsolved.
      index_integer_spelling?(vname) ->
        acc

      MapSet.member?(seen, vname) ->
        # A constructor payload type can initially be open because an omitted
        # implicit slot precedes it in the constructor telescope (`Cons`'s head
        # has type `a`). A later occurrence in a computed index often supplies
        # the closed domain (`plus(left, right)` pins both to Nat). Retain first-
        # appearance ordering, but refine that provisional open type when the
        # later evidence is closed. Keeping the open term leaks the constructor's
        # private telescope variable into the enclosing constructor and produces
        # an out-of-frame Core `{:var, k}`.
        ordered2 =
          Enum.map(ordered, fn
            {^vname, old_type} ->
              if not Term.closed?(old_type) and Term.closed?(type), do: {vname, type}, else: {vname, old_type}

            entry ->
              entry
          end)

        {ordered2, seen}

      vname == "Type" ->
        acc

      atom == fam ->
        acc

      Inductive.get_ctor(env, atom) ->
        acc

      Inductive.family?(env, atom) ->
        acc

      Env.get_def(env, atom) ->
        acc

      true ->
        {ordered ++ [{vname, type}], MapSet.put(seen, vname)}
    end
  end

  defp index_integer_spelling?(name) when is_binary(name) do
    case Integer.parse(name) do
      {_value, ""} -> true
      _ -> false
    end
  end

  # -- surface index/type expr → Core, with a de Bruijn scope -----------------

  # `ctx` (5th arg, spec 2026-07-08 §7.3): the kernel typing context for the
  # enclosing fn's parameters, threaded ONLY by the return-type lowering in
  # `function_signature` (every other caller keeps the 4-arg form → nil). When
  # present, a function-call node whose head is a term-level global carrying
  # implicit (erased) parameters delegates to the term-position implicit-app
  # machinery instead of lowering as a bare explicit-args spine. Crossing a
  # binder-introducing form (pi/sigma/arrow) NULLs the ctx for that sub-lowering
  # (the scope gains binders the kernel context lacks — §7.3 item 4).
  @doc """
  The single canonical type→Core lowering, shared by the live signature path
  (`register_signature`/`elaborate_param_telescope`) and the legacy
  `Elaborator.elaborate_type/3`, which delegates here. `scope` names the binders
  in de Bruijn order (most-recent first); there is no family-relative context, so
  `fam`/`ctx` are `nil` (used only defensively for family self-reference and
  return-type implicit insertion). Lowers a type expression — including a numeric
  index like `Bounded(5)` → `{:nat_lit, 5}` — to a Core term.
  """
  @spec lower_type(tuple(), [String.t()], Env.t()) :: {:ok, tuple()} | {:error, term()}
  def lower_type(ast, scope, env), do: idx_to_core(ast, scope, nil, env, nil)

  @doc """
  The free type variables of one or more surface type ASTs, in order of first
  appearance — the same kind-`Type`, family-aware collection Idris-style
  auto-generalization uses (`auto_generalize/3`), but with an empty bound set.

  Passed as the `scope` to `lower_type/3`, these names lower to positional
  `{:var, idx}` de Bruijn indices instead of distinct global neutrals, so two
  signatures that differ only by a consistent renaming of their type variables
  lower to identical Core terms and compare equal under kernel conversion.
  """
  @spec free_type_vars([tuple()], Env.t()) :: [String.t()]
  def free_type_vars(type_asts, env) do
    {ordered, _seen} =
      type_asts
      |> Enum.reject(&is_nil/1)
      |> Enum.reduce({[], MapSet.new()}, fn ast, acc ->
        collect_type_vars(ast, MapSet.new(), env, acc)
      end)

    ordered
  end

  # Classify an index NAME node as a numeral, since a name STARTING WITH A DIGIT
  # can only be a stringified numeric token from the type parser (Cure identifiers
  # never start with a digit) — never a binder. Returns:
  #   {:ok, n}     — a non-negative integer Nat index (compact `nat_lit`)
  #   {:error, r}  — a numeral-shaped name that is not a valid Nat index
  #                  (fractional or negative), an error rather than a phantom global
  #   :not_numeric — a real (non-numeric) name; fall through to binder/global lookup
  #
  # The lexer already normalizes hex (`0x…`), binary (`0b…`) and underscored
  # integers to a decimal digit-string, so those arrive as all-digits. Scientific
  # notation lexes as a float and arrives stringified (`1e6` → "1.0e6"); an
  # integer-valued float is a valid index, a genuinely fractional one is rejected.
  defp numeric_index_value(name) when is_binary(name) do
    cond do
      String.match?(name, ~r/\A[0-9]+\z/) ->
        {:ok, String.to_integer(name)}

      String.match?(name, ~r/\A[0-9]/) ->
        case Float.parse(name) do
          {f, ""} when f >= 0.0 ->
            t = trunc(f)
            if t * 1.0 == f, do: {:ok, t}, else: {:error, {:non_integer_index, name}}

          _ ->
            {:error, {:non_integer_index, name}}
        end

      true ->
        :not_numeric
    end
  end

  defp numeric_index_value(_), do: :not_numeric

  defp idx_to_core(ast, scope, fam, env, ctx \\ nil)

  defp idx_to_core({:variable, _meta, "Type"}, _scope, _fam, _env, _ctx), do: {:ok, {:type, 0}}

  defp idx_to_core({:variable, _meta, name} = node, scope, _fam, env, _ctx) do
    # A numeric literal in a dependent type index — the `5` in `Bounded(5)`, the
    # `0x110000` Char bound in `Bounded(1114112)`, a scientific `1e6`. The lexer's
    # numeric token is stringified into a NAME node by the type parser. It can never
    # be a binder (you cannot bind `5`), so it is unambiguously a compact `Nat`
    # literal regardless of scope — the surface half of the compact-Nat kernel path
    # (Lean/Agda: a numeral in index position is a `Nat`). Without this it fell
    # through to a phantom `{:global, :"5"}`.
    case numeric_index_value(name) do
      {:ok, n} ->
        {:ok, {:nat_lit, n}}

      {:error, reason} ->
        case reason do
          {:non_integer_index, ^name} ->
            {:error, {:non_integer_index, index_problem_details(node, value: name)}}

          _ ->
            {:error, reason}
        end

      :not_numeric ->
        cond do
          (idx = Enum.find_index(scope, &(&1 == name))) != nil ->
            {:ok, {:var, idx}}

          true ->
            case resolve_index_name(name, env) do
              {:ambiguous_name, atom, mods} ->
                {:error, {:ambiguous_name, atom, mods}}

              {:retired_process_type, legacy} ->
                info = Cure.MetaAST.Metadata.source_info(elem(node, 1))

                {:error,
                 {:retired_process_type,
                  %{
                    name: legacy,
                    span: info && (info.name || info.whole)
                  }}}

              node ->
                {:ok, node}
            end
        end
    end
  end

  defp idx_to_core({:function_call, fmeta, args}, scope, fam, env, ctx) do
    cond do
      Keyword.get(fmeta, :function_type) ->
        arrow_to_pi(args, scope, fam, env)

      Keyword.fetch!(fmeta, :name) == "Tuple" ->
        build_telescope_type(
          Enum.zip(List.duplicate("_", length(args)), args),
          scope,
          fam,
          env
        )

      Keyword.fetch!(fmeta, :name) == "Effect" ->
        lower_effect_former(args, scope, fam, env, ctx)

      true ->
        lower_applied_type(fmeta, args, scope, fam, env, ctx)
    end
  end

  # Binder-introducing forms (sigma/pi/arrow) sub-lower with the 4-arg form:
  # the ctx is NULLed under their binders (spec §7.3 item 4). `Sigma(x: D, U)`
  # lowers to the builtin inductive `Sigma(D, λx:D. U)`: `body` was elaborated with
  # `bname` in scope, so it is already in the frame of one new lambda binder, and
  # wrapping it under `{:lam, Cure.Core.Grade.unrestricted(), dom, body}` is exactly that frame.
  defp idx_to_core({:sigma_type, meta, [dom_ast, body_ast]}, scope, fam, env, _ctx)
       when is_list(meta) do
    bname = Keyword.fetch!(meta, :binder)

    with {:ok, dom} <- idx_to_core(dom_ast, scope, fam, env),
         {:ok, body} <- idx_to_core(body_ast, [bname | scope], fam, env) do
      {:ok, {:data, sigma_family_name(env), [dom, {:lam, Cure.Core.Grade.unrestricted(), dom, body}], []}}
    end
  end

  # A refinement is an ordinary dependent pair in Core: the value and a proof of
  # the proposition about that value. Solvers receive no trusted representation.
  #
  # Surface sugar (§3a level 1): the refinement bar takes the bare boolean
  # condition and reflects it, like Liquid Haskell / F* / Lean. A comparison or
  # boolean-connective clause has type `Bool`, so it is wrapped in `IsTrue(φ)`
  # before lowering — producing the same Σ as an explicit `IsTrue(φ)` clause. A
  # `Type`-valued clause (a named predicate / proposition) is left unchanged.
  defp idx_to_core(
         {:refinement_type, meta, [dom_ast, proposition_ast]},
         scope,
         fam,
         env,
         _ctx
       )
       when is_list(meta) do
    bname = Keyword.fetch!(meta, :binder)

    with {:ok, dom} <- idx_to_core(dom_ast, scope, fam, env),
         {:ok, proposition} <-
           idx_to_core(reflect_boolean_proposition(proposition_ast), [bname | scope], fam, env) do
      {:ok, {:data, sigma_family_name(env), [dom, {:lam, Cure.Core.Grade.unrestricted(), dom, proposition}], []}}
    end
  end

  # A flat tuple TYPE `Tuple(T1, …, Tn)` unfolds to the UNIT-TERMINATED nested Σ
  # telescope `Sigma(T1, λb1. Sigma(T2, λb2. … Sigma(Tn, λbn. Unit)))` — reusing the
  # kernel's binary Σ (no new kernel surface). The terminating `Unit` is what emit
  # keys on to flatten the whole spine to a flat BEAM tuple (spec §3.4). Each binder
  # `bi` is threaded into scope so a later position may depend on an earlier one
  # (dependent telescope); anonymous positions carry `"_"`.
  defp idx_to_core({:tuple_type, meta, type_asts}, scope, fam, env, _ctx) do
    binders = Keyword.get(meta, :binders) || List.duplicate("_", length(type_asts))
    build_telescope_type(Enum.zip(binders, type_asts), scope, fam, env)
  end

  # A dependent function type `(x1: D1, …, xn: Dn) -> R` becomes the Π
  # `Π(x1:D1). … Π(xn:Dn). R`. Each domain is elaborated with the earlier binders
  # in scope, and the codomain with all of them, so `(n: N) -> P(n)` resolves the
  # `n` in `P(n)` as the Π-bound variable (de Bruijn `{:var, 0}`). Direct analog of
  # the `sigma_type` binder threading above; `nil` binders (anonymous domains, from
  # a mixed `(a, x: B) -> …`) push a placeholder so indices stay aligned.
  defp idx_to_core({:pi_type, meta, asts}, scope, fam, env, _ctx) when is_list(meta) do
    names = Keyword.fetch!(meta, :binders)
    {domains, [ret_ast]} = Enum.split(asts, length(asts) - 1)

    folded =
      Enum.zip(names, domains)
      |> Enum.reduce_while({:ok, [], scope}, fn {name, dom_ast}, {:ok, rev, sc} ->
        case idx_to_core(dom_ast, sc, fam, env) do
          {:ok, dom} -> {:cont, {:ok, [dom | rev], [name || :_ | sc]}}
          {:error, _} = err -> {:halt, err}
        end
      end)

    with {:ok, rev_doms, inner_scope} <- folded,
         {:ok, ret} <- idx_to_core(ret_ast, inner_scope, fam, env) do
      {:ok, Enum.reduce(rev_doms, ret, fn dom, acc -> {:pi, Cure.Core.Grade.unrestricted(), dom, acc} end)}
    end
  end

  # A qualified TYPE reference (`Std.Nat` / `Std.Nat.Nat`, no call parens) OR a
  # projection `p.1` / `p.2` used in a type position (e.g. `SF(as, bs, p.1)`).
  # For a projection, lower to the Std.Sigma projection global exactly as the
  # term-position `sigma_projection` does — the ctx threaded from the return-type
  # position (spec 2026-07-08 §7.3) is REQUIRED to solve the erased implicits, so
  # `ctx` must not be discarded. A `.1`/`.2` reached with `ctx == nil` (a non-
  # return-type index/telescope position that does not thread ctx) has no frame to
  # solve the implicits and errors precisely — a spec §7.5-class residual.
  defp idx_to_core({:attribute_access, meta, [inner_ast]} = node, scope, _fam, env, ctx) do
    attr = Keyword.fetch!(meta, :attribute)
    dotted = Cure.Compiler.Parser.dotted_path_of(node)

    cond do
      # A qualified TYPE reference like Std.Nat / Std.Nat.Nat (no call parens).
      is_binary(dotted) and match?({:ok, _}, Cure.Elab.Resolution.resolve_qualified(env, dotted, :type)) ->
        {:ok, key} = Cure.Elab.Resolution.resolve_qualified(env, dotted, :type)

        if Inductive.family?(env, key) do
          {:ok, {:data, key, [], []}}
        else
          {:ok, {:global, key}}
        end

      attr in ["1", "2"] and not is_nil(ctx) ->
        gname = if attr == "1", do: :sigma_first, else: :sigma_second

        with {:ok, term, _type} <-
               Cure.Elab.Elaborator.elaborate_implicit_global_app(env, gname, [inner_ast], scope, ctx) do
          {:ok, term}
        end

      attr in ["1", "2"] ->
        {:error, {:sigma_projection_needs_ctx, index_problem_details(node, projection: attr)}}

      true ->
        {:error, {:bad_projection, attr}}
    end
  end

  # An anonymous union. Its family was already declared by the pre-pass in
  # `elaborate/2` (idx_to_core cannot thread a mutated Env back out), so this only
  # recomputes the content-derived key and looks it up. A one-member union of a TYPE
  # member collapses to that member's Core term — no family exists for it.
  defp idx_to_core({:union_type, _meta, members}, scope, _fam, env, _ctx) do
    with {:ok, ms} <- Cure.Elab.Union.canonicalise(members, scope, env) do
      case ms do
        [%{payload: payload}] when payload != nil -> {:ok, payload}
        _ -> {:ok, {:data, Cure.Elab.Union.family_key(ms, env), [], []}}
      end
    end
  end

  # A comparison / boolean-connective PROPOSITION in an index position — the `n > 0`
  # inside `IsTrue(n > 0)` (decidable-boolean reflection, spec 2026-07-18). The parser
  # reparses such a type-application argument with the expression parser, so it arrives
  # as an expression `{:binary_op, ...}` with `{:literal, ...}` operands rather than a
  # type atom. We lower it to the SAME builtin-op spine the term elaborator's
  # `build_binop` produces — the Int builtins (`Std.Builtin#int_gt` etc.) for Int
  # operands, the Float builtins (`float_gt` etc.) when an operand is a float literal,
  # or the bare `and`/`or` connective globals — so a closed comparison folds to
  # `Std.Bool#True` by pure computation and `Confirmed : IsTrue(True())` inhabits it.
  # Operands are lowered FIRST so the dispatch can see whether a `{:float_lit, _}` is
  # present; this mirrors `build_binop`'s Int→int_*/Float→float_* split and keeps the
  # comparison well-typed on Float operands (`float_le(0.0, q) : Bool`), which the Int
  # op would reject as `{:float_type}` vs `{:int_type}`. A comparison of two Float
  # VARIABLES with no literal operand cannot be detected here (scope carries names, not
  # types) and stays on the int op: it simply will not type-check or discharge — a
  # documented residual, never unsound. Operands recurse through `idx_to_core`, so
  # nested connectives compose.
  defp idx_to_core({:binary_op, meta, [l_ast, r_ast]} = node, scope, fam, env, ctx) do
    op = Keyword.fetch!(meta, :operator)

    with {:ok, l} <- idx_to_core(l_ast, scope, fam, env, ctx),
         {:ok, r} <- idx_to_core(r_ast, scope, fam, env, ctx) do
      case index_binop_global(op, float_operands?(l, r)) do
        {:ok, global} ->
          {:ok, {:app, {:app, {:global, global}, l}, r}}

        {:error, {:unsupported_index_operator, ^op}} ->
          {:error, {:unsupported_index_operator, index_problem_details(node, operator: op)}}
      end
    end
  end

  # An expression-parsed numeric literal reaching an index position — only produced by
  # the propositional reparse above (ordinary type-position numerals arrive as stringified
  # NAME nodes handled by the `{:variable, ...}` clause). An integer operand of an Int
  # comparison must be a real `{:int_lit, _}` so the kernel's `int_*` fold fires; a Nat
  # literal (`{:nat_lit, _}`, `{:vnat, _}`) would leave the spine stuck.
  defp idx_to_core({:literal, meta, value} = node, _scope, _fam, _env, _ctx) do
    case Keyword.get(meta, :subtype) do
      :integer ->
        {:ok, {:int_lit, value}}

      :float ->
        {:ok, {:float_lit, value}}

      :char when is_integer(value) and value >= 0 and value <= 0x10FFFF ->
        {:ok, {:bounded_lit, value}}

      :char ->
        {:error, {:char_literal_out_of_range, index_problem_details(node, value: value)}}

      other ->
        {:error, {:unsupported_index_literal, index_problem_details(node, subtype: other, value: value)}}
    end
  end

  defp idx_to_core(other, _scope, _fam, _env, _ctx),
    do: {:error, {:unsupported_index_expr, index_problem_details(other)}}

  defp index_problem_details(expression, extra \\ []) do
    %{
      expression: expression,
      span: index_expression_span(expression),
      shape: index_expression_shape(expression)
    }
    |> Map.merge(Map.new(extra))
  end

  defp index_expression_span({_tag, meta, _children}) when is_list(meta) do
    case Cure.MetaAST.Metadata.source_info(meta) do
      %Cure.MetaAST.SourceInfo{whole: %Cure.Diagnostic.Span{} = span} -> span
      _ -> nil
    end
  end

  defp index_expression_span(_expression), do: nil

  defp index_expression_shape({tag, _meta, _children}) when is_atom(tag), do: tag
  defp index_expression_shape(_expression), do: :unknown

  # A comparison is over Float when either lowered operand is a float literal. This is
  # the only operand-type signal available in an index position (the scope threaded
  # through `idx_to_core` is a list of binder NAMES, not typed context), and it covers
  # every refinement whose bound is a literal — `x > 0.0`, `0.0 <= p`, `p <= 1.0`.
  defp float_operands?(l, r), do: float_operand?(l) or float_operand?(r)
  defp float_operand?({:float_lit, _}), do: true
  defp float_operand?(_), do: false

  # Operator symbol + Float-operand flag → the Core global its index-position lowering
  # applies. Comparisons map to the Int builtin op (registered as `Std.Builtin#int_*`,
  # folding via `Eval.fold`) or, when the flag is set, the Float twin (`Std.Builtin#float_*`)
  # so a Float comparison stays well-typed. The boolean connectives map to the qualified
  # `Std.Bool#and`/`#or` defs — the SAME spelling the function-call form (`` `and`(l, r) ``)
  # resolves to, so an operator-written conjunction proposition is recognized by the
  # conjunction-elimination candidate source in `Cure.Elab.ProofSearch` (which matches the
  # resolved `Std.Bool#and` head); the flag does not affect them. Emitting the bare
  # `:and`/`:or` the term-level `build_binop` uses would leave operator-`and` refinements
  # undischargeable, since the projection lemmas speak the qualified `and`.
  defp index_binop_global(:<, false), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :int_lt)}
  defp index_binop_global(:<, true), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :float_lt)}
  defp index_binop_global(:<=, false), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :int_le)}
  defp index_binop_global(:<=, true), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :float_le)}
  defp index_binop_global(:>, false), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :int_gt)}
  defp index_binop_global(:>, true), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :float_gt)}
  defp index_binop_global(:>=, false), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :int_ge)}
  defp index_binop_global(:>=, true), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :float_ge)}
  defp index_binop_global(:==, false), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :int_eq)}
  defp index_binop_global(:==, true), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :float_eq)}
  defp index_binop_global(:!=, false), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :int_ne)}
  defp index_binop_global(:!=, true), do: {:ok, Cure.Elab.Name.qualify("Std.Builtin", :float_ne)}
  defp index_binop_global(:and, _), do: {:ok, Cure.Elab.Name.qualify("Std.Bool", :and)}
  defp index_binop_global(:or, _), do: {:ok, Cure.Elab.Name.qualify("Std.Bool", :or)}
  defp index_binop_global(op, _), do: {:error, {:unsupported_index_operator, op}}

  # Wrap a `Bool`-typed refinement clause in `IsTrue(·)` (§3a level 1). Only
  # operators with a Bool-producing index lowering reflect;
  # every other clause — a `Type`-valued predicate application, an already-explicit
  # `IsTrue(…)`, or an arithmetic misuse that should be rejected as ill-sorted —
  # passes through untouched. The wrapper node is exactly what the parser yields
  # for an explicit `IsTrue(φ)`, so lowering (and `IsTrue` name resolution) is
  # shared verbatim.
  defp reflect_boolean_proposition({:binary_op, meta, _} = prop) do
    op = Keyword.fetch!(meta, :operator)

    if match?({:ok, _global}, index_binop_global(op, false)) do
      {:function_call, [name: "IsTrue"], [prop]}
    else
      prop
    end
  end

  defp reflect_boolean_proposition(prop), do: prop

  # Surface `Effect(T)` lowers to the kernel's inert effect type former
  # `{:effect_type, ⟦T⟧}` (design 2026-07-09-effect-type-former §3). `Effect` is a
  # kernel PRIMITIVE type former (`Type ℓ → Type ℓ`), NOT an inductive family, so —
  # unlike List/Bounded/Sigma — there is no family-id to bind under the `@builtin`
  # tag registry (`Inductive.register_builtin` maps a key to a family-id validated
  # by `Core.Builtins`). It is therefore recognised by NAME here, mirroring the
  # dedicated `:sigma_type` / `:tuple_type` / `:pi_type` surface forms that hardcode
  # their target Core node. The single argument is lowered through the SAME
  # `idx_to_core` (so `Effect(List(Int))` recurses); a non-type argument is caught
  # downstream by the kernel's `Effect : Type ℓ → Type ℓ` formation rule, not here.
  defp lower_effect_former([arg], scope, fam, env, ctx) do
    with {:ok, core} <- idx_to_core(arg, scope, fam, env, ctx) do
      {:ok, {:effect_type, core}}
    end
  end

  defp lower_effect_former(args, _scope, _fam, _env, _ctx),
    do: {:error, {:effect_arity, length(args)}}

  # The general applied-type spine lowering (`Name(args)`): a qualified family, an
  # applied bound var, a family/ctor, or an opaque global. Split out of the
  # `{:function_call, …}` clause so the `Effect` special-case can sit beside it.
  # Extracted by core-let-binder's `cond` dispatch. Body is THIS branch's version:
  # it carries the qualified-name degrade (`Std.Option` -> `Option`) that the
  # extracted base body did not have.
  defp lower_applied_type(fmeta, args, scope, fam, env, ctx) do
    raw_name = Keyword.fetch!(fmeta, :name)

    # A qualified head (`Std.Map`, from `Mod.Name(args)`) is first offered to the
    # module-aware type resolver. When it places the name we emit `{:data, key, …}`
    # in the cond below. When it can't — e.g. `Std.Option`, which lowers to a plain
    # `{:global, :Option}` rather than a registered inductive family — the name
    # DEGRADES to its bare tail (`Std.Option` → `Option`) so every downstream check
    # (implicit-global, family, ctor, global) resolves it EXACTLY as the unqualified
    # spelling would. Without this degrade a qualified applied type lowered to an
    # opaque `{:global, :"Std.Option"}` that never converts against the unqualified
    # `{:global, :Option}` — a silent qualified-vs-unqualified type split. For an
    # unqualified name `String.split/2` returns `[name]`, so this is a no-op there.
    qualified_key =
      if String.contains?(raw_name, ".") do
        Cure.Elab.Resolution.resolve_qualified(env, raw_name, :type)
      else
        :error
      end

    name =
      case qualified_key do
        {:ok, _} -> raw_name
        :error -> raw_name |> String.split(".") |> List.last()
      end

    atom = String.to_atom(name)

    # Type-position implicit insertion (spec §7): a term-level global whose
    # signature carries erased (implicit) parameters cannot lower as a bare
    # explicit-args spine — the kernel would see an under-applied application
    # (the `b(first(p))` motive gap). With a typing context threaded in
    # (return-type lowering only), delegate the whole application to the
    # term-position machinery. A local binder of the same name shadows the
    # global (mirrors the applied-bound-var cond branch below), and families/
    # ctors never carry def quantities, so this misses them by construction.
    #
    # The SAME bidirectional delegation is also the only way to lower an
    # application carrying a bare `fn(y) -> …` LAMBDA argument (E10a): the
    # syntax-directed `idx_to_core` cannot lower a lambda — an unannotated binder
    # has no domain until it is CHECKED against the callee's Π-domain, which only
    # the bidirectional term elaborator supplies (`bidir_app_slot` checks the
    # lambda at `(Dec) -> Eff` when lowering `bind(m, fn(y) -> Pure(y))`). Without
    # this the lambda hit the `{:lambda, …}` catch-all as `:unsupported_index_expr`.
    # Guarded on the head being a real def (get_def carries `:quantities`) so a
    # family/ctor applied to a lambda is left to its own path, and on `ctx` (a
    # non-return-type index position threads none — an acceptable §7.5-class
    # residual, mirroring `:sigma_projection_needs_ctx`).
    # A bare name resolvable to a return-type/index typing context (`ctx`) that is
    # not shadowed by a local binder is eligible for the two term-delegating
    # lowerings below.
    delegable? = ctx != nil and Enum.find_index(scope, &(&1 == name)) == nil

    # Type-directed OVERLOAD resolution in index position (E11-Stage-2 + E11
    # crash). A bare overloaded name (≥2 discriminated/cross-module members) reached
    # `applied_def_key`'s pre-overload resolver, which mis-picked an ambient
    # same-name provider (`plus(MkM …)` → `Std.Nat#plus`, then a raw ι crash) or
    # reported `:ambiguous_name`. Route it through the SAME overload machinery as
    # term position so the argument types prune to the intended member. A bare name
    # with a single local/direct winner collapses to <2 candidates and never
    # reaches here. Guarded on `not qualified` (a dotted head is resolved by name)
    # to mirror the term-position `not String.contains?` guard.
    overload_cands =
      if delegable? and not String.contains?(raw_name, ".") do
        Cure.Elab.Resolution.overload_candidates(env, atom)
      else
        []
      end

    cond do
      length(overload_cands) >= 2 ->
        with {:ok, term, _result_type} <-
               Cure.Elab.Elaborator.elaborate_overloaded_app(
                 env,
                 atom,
                 args,
                 Keyword.get(fmeta, :arg_labels),
                 scope,
                 ctx,
                 overload_cands
               ) do
          {:ok, term}
        end

      delegable? and
          (implicit_global?(env, atom) or
             (args_contain_lambda?(args) and term_level_def?(env, atom))) ->
        with {:ok, term, _result_type} <-
               Cure.Elab.Elaborator.elaborate_implicit_global_app(env, atom, args, scope, ctx) do
          {:ok, term}
        end

      true ->
        family_key = applied_family_key(atom, fam, env, qualified_key)
        definition_key = if is_nil(family_key), do: applied_def_key(env, raw_name, atom), else: nil

        with {:ok, core_args} <-
               lower_applied_arguments(args, family_key, definition_key, scope, fam, env, ctx) do
          case expand_typealias_application(env, atom, core_args) do
            {:ok, expanded} ->
              {:ok, expanded}

            :not_typealias ->
              lower_applied_type_head(atom, raw_name, args, core_args, fam, env, qualified_key, scope, ctx)
          end
        end
    end
  end

  defp applied_family_key(_atom, _fam, env, {:ok, key}) do
    if Inductive.family?(env, key), do: key, else: nil
  end

  defp applied_family_key(atom, fam, env, :error) do
    if atom == fam or Inductive.family?(env, atom),
      do: Env.resolve_key(env, env.families, atom),
      else: nil
  end

  defp lower_applied_arguments(args, nil, definition, scope, fam, env, ctx) when is_atom(definition) do
    case Env.get_def(env, definition) do
      %{type: type} -> lower_definition_arguments(args, type, scope, fam, env, ctx)
      _ -> map_idx_to_core(args, scope, fam, env, ctx)
    end
  end

  defp lower_applied_arguments(args, nil, _definition, scope, fam, env, ctx),
    do: map_idx_to_core(args, scope, fam, env, ctx)

  # Lower a family application left-to-right against its dependent telescope.
  # This supplies the expected type of each argument to nested constructors, so
  # an omitted implicit constructor index can be recovered from the enclosing
  # family slot (`ListMember(MachineState(2), Accepted(rs, cs), ...)`). Merely
  # copying the written constructor arguments produced malformed Final Core and
  # deferred the failure to a bare kernel `:ctor_arity` during body checking.
  defp lower_applied_arguments(args, family, _definition, scope, fam, env, ctx) do
    tele = (Inductive.param_telescope(env, family) || []) ++ (Inductive.index_telescope(env, family) || [])

    if length(args) == length(tele) do
      Enum.zip(args, tele)
      |> Enum.reduce_while({:ok, []}, fn {arg, {_name, dom}}, {:ok, actuals} ->
        expected = Subst.instantiate(dom, actuals)

        case idx_to_core_expected(arg, expected, scope, fam, env, ctx) do
          {:ok, core} -> {:cont, {:ok, actuals ++ [core]}}
          {:error, _} = error -> {:halt, error}
        end
      end)
    else
      map_idx_to_core(args, scope, fam, env, ctx)
    end
  end

  defp lower_definition_arguments(args, type, scope, fam, env, ctx) do
    if pi_arity(type) == length(args) do
      Enum.reduce_while(args, {:ok, [], type}, fn arg, {:ok, actuals, {:pi, _grade, dom, cod}} ->
        case idx_to_core_expected(arg, dom, scope, fam, env, ctx) do
          {:ok, core} -> {:cont, {:ok, actuals ++ [core], Subst.instantiate(cod, [core])}}
          {:error, _} = error -> {:halt, error}
        end
      end)
      |> case do
        {:ok, actuals, _rest} -> {:ok, actuals}
        {:error, _} = error -> error
      end
    else
      map_idx_to_core(args, scope, fam, env, ctx)
    end
  end

  defp idx_to_core_expected({:function_call, fmeta, args} = ast, expected, scope, fam, env, ctx) do
    atom = fmeta |> Keyword.fetch!(:name) |> String.split(".") |> List.last() |> String.to_atom()
    key = Env.resolve_key(env, env.ctors, atom)

    if Inductive.get_ctor(env, key) do
      with {:ok, term} <-
             complete_index_constructor_ast(key, args, expected, scope, fam, env, ctx) do
        {:ok, term}
      else
        _ -> idx_to_core(ast, scope, fam, env, ctx)
      end
    else
      idx_to_core(ast, scope, fam, env, ctx)
    end
  end

  # Signature registration lowers parameter types before a kernel context has
  # been built. In that phase the ordinary surface lowering is authoritative;
  # expected-type-directed compact literals are revisited once a real context
  # exists (constructor results and checked bodies). Never attempt NbE against
  # a synthetic context that would lose the surrounding parameter telescope.
  defp idx_to_core_expected(ast, _expected, scope, fam, env, nil),
    do: idx_to_core(ast, scope, fam, env, nil)

  defp idx_to_core_expected({:variable, _meta, spelling} = ast, expected, scope, fam, env, ctx) do
    case numeric_index_value(spelling) do
      {:ok, value} ->
        expected_value = Eval.eval(expected, Context.env(ctx))
        bounded = {:bounded_lit, value}

        case Kernel.check(ctx, bounded, expected_value) do
          :ok -> {:ok, bounded}
          {:error, {:bounded_lit_out_of_range, _value, _bound}} = error -> error
          {:error, _not_bounded} -> idx_to_core(ast, scope, fam, env, ctx)
        end

      _ ->
        idx_to_core(ast, scope, fam, env, ctx)
    end
  end

  defp idx_to_core_expected(ast, _expected, scope, fam, env, ctx),
    do: idx_to_core(ast, scope, fam, env, ctx)

  defp complete_index_constructor_ast(cname, explicit, expected, scope, fam, env, ctx) do
    ctor = Inductive.get_ctor(env, cname)
    plicities = Inductive.plicities_of(ctor)

    if Enum.count(plicities, &(&1 == :explicit)) == length(explicit) do
      pc = Inductive.param_count(env, Inductive.ctor_family(env, cname))
      {mctx, seed} = fresh_index_seed(MetaCtx.new(), pc + length(ctor.args), [])
      {params, field_seed} = Enum.split(seed, pc)
      frame = params ++ field_seed

      result =
        {:data, Inductive.ctor_family(env, cname),
         Enum.map(Map.get(ctor, :result_params, []), &Subst.instantiate(&1, frame)),
         Enum.map(ctor.result_indices, &Subst.instantiate(&1, frame))}

      case Unify.unify(result, expected, mctx, env) do
        {:ok, solved} ->
          solved_params = Enum.map(params, &Unify.zonk(&1, solved))
          args = {ctor.args, plicities, explicit, field_seed, solved_params, solved, scope, fam, env, ctx}

          case lower_complete_index_constructor_fields(args, false) do
            {:ok, values} ->
              {:ok, {:ctor, cname, values}}

            :unsolved ->
              case lower_complete_index_constructor_fields(args, true) do
                {:ok, values} -> {:ok, {:ctor, cname, values}}
                _ -> :error
              end

            :error ->
              :error
          end

        {:error, _} ->
          :error
      end
    else
      :error
    end
  end

  defp lower_complete_index_constructor_fields(
         {fields, plicities, explicit, seeds, params, mctx, scope, fam, env, ctx},
         solve_field_types
       ) do
    case lower_index_constructor_fields(
           fields,
           plicities,
           explicit,
           seeds,
           params,
           mctx,
           scope,
           fam,
           env,
           ctx,
           solve_field_types,
           []
         ) do
      {:ok, lowered, final_mctx} ->
        values = Enum.map(lowered, &Unify.zonk(&1, final_mctx))
        if Enum.any?(values, &index_term_has_meta?/1), do: :unsolved, else: {:ok, values}

      _ ->
        :error
    end
  end

  defp lower_index_constructor_fields(
         [],
         [],
         [],
         [],
         _params,
         mctx,
         _scope,
         _fam,
         _env,
         _ctx,
         _solve_field_types,
         acc
       ),
       do: {:ok, Enum.reverse(acc), mctx}

  defp lower_index_constructor_fields(
         [{_name, _dom} | fields],
         [:implicit | plicities],
         explicit,
         [seed | seeds],
         params,
         mctx,
         scope,
         fam,
         env,
         ctx,
         solve_field_types,
         acc
       ) do
    lower_index_constructor_fields(
      fields,
      plicities,
      explicit,
      seeds,
      params,
      mctx,
      scope,
      fam,
      env,
      ctx,
      solve_field_types,
      [Unify.zonk(seed, mctx) | acc]
    )
  end

  defp lower_index_constructor_fields(
         [{_name, dom} | fields],
         [:explicit | plicities],
         [ast | explicit],
         [seed | seeds],
         params,
         mctx,
         scope,
         fam,
         env,
         ctx,
         solve_field_types,
         acc
       ) do
    prior = Enum.reverse(acc)
    expected = dom |> Subst.instantiate(params ++ prior) |> Unify.zonk(mctx)

    with {:ok, value} <- idx_to_core_expected(ast, expected, scope, fam, env, ctx),
         {:ok, typed} <- maybe_solve_index_constructor_field_type(solve_field_types, value, expected, mctx, env, ctx),
         {:ok, solved} <- Unify.unify(seed, value, typed, env) do
      lower_index_constructor_fields(
        fields,
        plicities,
        explicit,
        seeds,
        params,
        solved,
        scope,
        fam,
        env,
        ctx,
        solve_field_types,
        [value | acc]
      )
    end
  end

  defp lower_index_constructor_fields(
         _fields,
         _plicities,
         _explicit,
         _seeds,
         _params,
         _mctx,
         _scope,
         _fam,
         _env,
         _ctx,
         _solve_field_types,
         _acc
       ),
       do: :error

  # Expected-result solving can leave a constructor's hidden indices open when
  # they do not occur in its result (`PatternGroup(inner) : Pattern(StringC)`
  # forgets `inner`'s shape).  The explicit field still determines those metas
  # through its inferred type.  Solve that equation at the single expected-index
  # constructor path before accepting the field value; otherwise the unsolved
  # implicit is dropped and interface registration later reports only an opaque
  # dependent-index mismatch.
  defp maybe_solve_index_constructor_field_type(false, _value, _expected, mctx, _env, _ctx), do: {:ok, mctx}

  defp maybe_solve_index_constructor_field_type(true, _value, _expected, mctx, _env, nil), do: {:ok, mctx}

  defp maybe_solve_index_constructor_field_type(true, value, expected, mctx, env, ctx) do
    # This retry exists only to learn hidden constructor arguments that remain
    # open after result-index unification. Do not re-unify a field whose expected
    # type is already settled: a later proof field may normalize an index (for
    # example to `Nil`) and must not overwrite the explicit field that fixed it.
    if expected |> Unify.zonk(mctx) |> index_term_has_meta?() do
      case Kernel.infer(ctx, value) do
        {:ok, actual_value} ->
          actual = Quote.reify(actual_value, Context.length(ctx), Context.signature(ctx))
          Unify.unify(expected, actual, mctx, env)

        {:error, reason} ->
          {:error, reason}
      end
    else
      {:ok, mctx}
    end
  end

  defp fresh_index_seed(mctx, 0, acc), do: {mctx, Enum.reverse(acc)}

  defp fresh_index_seed(mctx, count, acc) do
    {mctx, id} = MetaCtx.fresh(mctx)
    fresh_index_seed(mctx, count - 1, [{:meta, id} | acc])
  end

  defp index_term_has_meta?({:meta, _}), do: true
  defp index_term_has_meta?(term) when is_tuple(term), do: term |> Tuple.to_list() |> Enum.any?(&index_term_has_meta?/1)
  defp index_term_has_meta?(term) when is_list(term), do: Enum.any?(term, &index_term_has_meta?/1)
  defp index_term_has_meta?(_term), do: false

  defp lower_applied_type_head(atom, raw_name, raw_args, core_args, fam, env, qualified_key, scope, ctx) do
    cond do
      match?({:ok, _}, qualified_key) ->
        {:ok, key} = qualified_key
        {params, indices} = Enum.split(core_args, Inductive.param_count(env, key))
        {:ok, {:data, key, params, indices}}

      # An applied BOUND variable — e.g. a higher-order parameter used as
      # `F(n)` where `F` is an implicit type-family parameter in scope. Resolve
      # the head against the de Bruijn scope; a local binder shadows a global,
      # so this is checked first. Without it `F(n)` became a dangling
      # `{:global, :F}`, and the call site's implicit substitution could never
      # turn `F` into a solvable metavariable (ledger #10 prerequisite).
      idx = Enum.find_index(scope, &(&1 == raw_name)) ->
        {:ok, Enum.reduce(core_args, {:var, idx}, fn a, acc -> {:app, acc, a} end)}

      atom == fam or applied_family_head?(env, atom, length(core_args)) ->
        atom = Env.resolve_key(env, env.families, atom)
        # Split the applied arguments into the family's parameters (prefix) and
        # indices (suffix); the kernel checks each slot against its own
        # telescope. param_count is 0 for parameter-free families (all indices).
        {params, indices} = Enum.split(core_args, Inductive.param_count(env, atom))
        {:ok, {:data, atom, params, indices}}

      Inductive.get_ctor(env, atom) ->
        lower_index_constructor(atom, raw_args, core_args, scope, fam, env, ctx)

      true ->
        # An applied plain (non-family, non-ctor) DEFINITION — e.g. `plus(a, b)`
        # in a dependent index. The head must resolve to its EXACT owned def key,
        # or δ-unfolding stays stuck and the application never reduces during
        # conversion. This mirrors the term-position resolution in
        # `elaborate_named_call`/`resolve_index_name`: a qualified head resolves
        # through the VALUE namespace, a bare head through `resolve_bare`, and a
        # genuinely ambiguous bare head is rejected (R7) rather than degraded to an
        # unresolvable `{:global, :bare}` that silently fails to convert.
        case applied_def_key(env, raw_name, atom) do
          {:ambiguous_name, a, mods} ->
            {:error, {:ambiguous_name, a, mods}}

          key ->
            {:ok, Enum.reduce(core_args, {:global, key}, fn a, acc -> {:app, acc, a} end)}
        end
    end
  end

  defp applied_family_head?(env, atom, supplied_arity) do
    if Inductive.family?(env, atom) do
      key = Env.resolve_key(env, env.families, atom)
      family = Inductive.get_family(env, key)
      family_arity = length(family.params) + length(family.indices)

      is_nil(Inductive.get_ctor(env, atom)) or family_arity == supplied_arity
    else
      false
    end
  end

  # Constructor values are legal inside dependent indices (`ThreadAccepted()`
  # inside an accepting-path state index). Surface syntax supplies only explicit
  # fields, while Core constructor nodes contain every implicit telescope slot as
  # well. The ordinary expression elaborator inserts those slots; the
  # syntax-directed type/index lowering historically copied only the written
  # arguments, leaking a bare `:ctor_arity` from interface registration.
  #
  # In a declaration result index the omitted implicit is commonly an already
  # bound outer index with the same telescope name (`n` in
  # `ThreadAccepted : ThreadState(n)`). Reconstruct that canonical Core spine
  # from the constructor plicities and the current de Bruijn scope. If a hidden
  # name is genuinely unavailable, preserve the old spine so the kernel reports
  # the honest unsolved/arity error rather than inventing a value.
  defp lower_index_constructor(atom, raw_args, explicit_args, scope, fam, env, ctx) do
    key = Env.resolve_key(env, env.ctors, atom)
    ctor = Inductive.get_ctor(env, key)
    plicities = Inductive.plicities_of(ctor)

    if Enum.count(plicities, &(&1 == :explicit)) == length(explicit_args) do
      inferred = infer_index_constructor_args(key, ctor, plicities, raw_args, scope, fam, env, ctx)

      case inferred do
        {:ok, args} ->
          {:ok, {:ctor, key, args}}

        :error ->
          case fill_index_constructor_args(ctor.args, plicities, explicit_args, scope, []) do
            {:ok, args} -> {:ok, {:ctor, key, args}}
            :unresolved -> {:ok, {:ctor, key, explicit_args}}
          end
      end
    else
      {:ok, {:ctor, key, explicit_args}}
    end
  end

  defp infer_index_constructor_args(_key, _ctor, _plicities, _explicit, _scope, _fam, _env, nil),
    do: :error

  defp infer_index_constructor_args(key, ctor, plicities, explicit, scope, fam, env, ctx) do
    pc = Inductive.param_count(env, Inductive.ctor_family(env, key))
    {mctx, seed} = fresh_index_seed(MetaCtx.new(), pc + length(ctor.args), [])
    {params, field_seed} = Enum.split(seed, pc)

    with {:ok, fields, solved} <-
           lower_index_constructor_fields(
             ctor.args,
             plicities,
             explicit,
             field_seed,
             params,
             mctx,
             scope,
             fam,
             env,
             ctx,
             false,
             []
           ) do
      values = Enum.map(fields, &Unify.zonk(&1, solved))
      if Enum.any?(values, &index_term_has_meta?/1), do: :error, else: {:ok, values}
    else
      _ -> :error
    end
  end

  defp fill_index_constructor_args([], [], [], _scope, acc), do: {:ok, Enum.reverse(acc)}

  defp fill_index_constructor_args(
         [{name, _type} | fields],
         [:implicit | plicities],
         explicit,
         scope,
         acc
       ) do
    case Enum.find_index(scope, &(&1 == Atom.to_string(name))) do
      nil -> :unresolved
      index -> fill_index_constructor_args(fields, plicities, explicit, scope, [{:var, index} | acc])
    end
  end

  defp fill_index_constructor_args(
         [_field | fields],
         [:explicit | plicities],
         [argument | explicit],
         scope,
         acc
       ),
       do: fill_index_constructor_args(fields, plicities, explicit, scope, [argument | acc])

  defp fill_index_constructor_args(_fields, _plicities, _explicit, _scope, _acc), do: :unresolved

  # Resolve an applied definition head to its exact registry key. `raw_name` is
  # the surface spelling (possibly dotted), `atom` its bare-tail atom. A qualified
  # head resolves through the value namespace to `Mod#name`; a bare head that is
  # uniquely present (locally or via one import) resolves to that key; a bare head
  # provided by ≥2 distinct modules with no unique winner is ambiguous. Anything
  # else keeps the current bare-atom behaviour (a genuinely-unknown name still
  # surfaces the ordinary `:unknown_global` downstream).
  defp applied_def_key(env, raw_name, atom) do
    cond do
      String.contains?(raw_name, ".") ->
        case Cure.Elab.Resolution.resolve_qualified(env, raw_name, :value) do
          {:ok, key} -> key
          :error -> Env.resolve_key(env, env.defs, atom)
        end

      match?({:ok, _}, Cure.Elab.Resolution.resolve_bare(env, atom)) ->
        {:ok, key} = Cure.Elab.Resolution.resolve_bare(env, atom)
        key

      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}

      true ->
        Env.resolve_key(env, env.defs, atom)
    end
  end

  # Parameterized type aliases are transparent lambdas in the Core signature.
  # Applied type lowering must beta-reduce those lambdas before the term reaches
  # the kernel; otherwise `Alias(a, b)` is mistaken for a runtime global
  # application and fails with `:unknown_global` (or, worse, can diverge from the
  # nullary-alias conversion path). Only aliases whose declared type is a
  # telescope of type parameters are unfolded here; ordinary term-level globals
  # remain opaque applications in type position.
  defp expand_typealias_application(env, name, args) do
    case Env.get_def(env, name) do
      %{type: type, body: body} when is_tuple(body) ->
        if typealias_parameter_count(type) == length(args) do
          expanded = beta_reduce_typealias(body, args)
          {:ok, expanded}
        else
          :not_typealias
        end

      _ ->
        :not_typealias
    end
  end

  defp typealias_parameter_count({:pi, _grade, {:type, _level}, codomain}) do
    1 + typealias_parameter_count(codomain)
  end

  defp typealias_parameter_count({:type, _level}), do: 0
  defp typealias_parameter_count(_other), do: -1

  defp beta_reduce_typealias(body, []) do
    body
  end

  defp beta_reduce_typealias({:lam, _grade, _domain, body}, [arg | rest]) do
    reduced = beta_substitute(body, 0, arg)
    beta_reduce_typealias(reduced, rest)
  end

  defp beta_reduce_typealias(body, _args), do: body

  # Binder-removing, capture-avoiding substitution for the alias beta step.
  # `Term.subst/3` deliberately keeps the replaced binder's index space intact,
  # which is correct for targeted unification substitution but not for reducing
  # `(fn x => body) arg`. This reducer decrements variables above the removed
  # binder and shifts inserted arguments only while crossing surviving binders.
  defp beta_substitute({:var, index}, depth, arg) do
    cond do
      index == depth -> Term.shift(arg, depth, 0)
      index > depth -> {:var, index - 1}
      true -> {:var, index}
    end
  end

  defp beta_substitute({:pi, grade, domain, codomain}, depth, arg) do
    {:pi, grade, beta_substitute(domain, depth, arg), beta_substitute(codomain, depth + 1, arg)}
  end

  defp beta_substitute({:lam, grade, domain, body}, depth, arg) do
    {:lam, grade, beta_substitute(domain, depth, arg), beta_substitute(body, depth + 1, arg)}
  end

  defp beta_substitute({:let, grade, type, value, body}, depth, arg) do
    {:let, grade, beta_substitute(type, depth, arg), beta_substitute(value, depth, arg),
     beta_substitute(body, depth + 1, arg)}
  end

  defp beta_substitute({:app, function, value}, depth, arg) do
    {:app, beta_substitute(function, depth, arg), beta_substitute(value, depth, arg)}
  end

  defp beta_substitute({:data, name, params, indices}, depth, arg) do
    {:data, name, Enum.map(params, &beta_substitute(&1, depth, arg)),
     Enum.map(indices, &beta_substitute(&1, depth, arg))}
  end

  defp beta_substitute({:ctor, name, fields}, depth, arg) do
    {:ctor, name, Enum.map(fields, &beta_substitute(&1, depth, arg))}
  end

  defp beta_substitute({:case, scrutinee, motive, branches}, depth, arg) do
    {:case, beta_substitute(scrutinee, depth, arg), beta_substitute(motive, depth, arg),
     Enum.map(branches, fn {name, arity, branch} ->
       {name, arity, beta_substitute(branch, depth + arity, arg)}
     end)}
  end

  defp beta_substitute({:effect_type, type}, depth, arg),
    do: {:effect_type, beta_substitute(type, depth, arg)}

  defp beta_substitute({:effect_pure, value}, depth, arg),
    do: {:effect_pure, beta_substitute(value, depth, arg)}

  defp beta_substitute({:effect_bind, effect, continuation}, depth, arg),
    do: {:effect_bind, beta_substitute(effect, depth, arg), beta_substitute(continuation, depth, arg)}

  defp beta_substitute(tuple, depth, arg) when is_tuple(tuple) do
    tuple
    |> Tuple.to_list()
    |> Enum.map(&beta_substitute(&1, depth, arg))
    |> List.to_tuple()
  end

  defp beta_substitute(list, depth, arg) when is_list(list),
    do: Enum.map(list, &beta_substitute(&1, depth, arg))

  defp beta_substitute(other, _depth, _arg), do: other

  defp build_telescope_type([], _scope, _fam, env),
    do: {:ok, {:data, Env.resolve_key(env, env.families, :Unit), [], []}}

  defp build_telescope_type([{bname, ast} | rest], scope, fam, env) do
    with {:ok, dom} <- idx_to_core(ast, scope, fam, env),
         {:ok, body} <- build_telescope_type(rest, [bname | scope], fam, env) do
      {:ok, {:data, sigma_family_name(env), [dom, {:lam, Cure.Core.Grade.unrestricted(), dom, body}], []}}
    end
  end

  defp sigma_family_name(env), do: Inductive.builtin(env, :sigma) || :Sigma

  # `(D1, …, Dn) -> R` (surface `Function(D1,…,Dn,R)`, tagged `function_type`)
  # becomes the non-dependent Π `Π(_:D1). … Π(_:Dn). R` — the native Core arrow the
  # kernel applies (`f(x)`) and checks lambdas against. Each type is elaborated in
  # the outer scope, then shifted past the arrow binders standing above it in the
  # nest (those binders are anonymous and unreferenced, so the shift only relocates
  # genuine outer-scope de Bruijn references).
  defp arrow_to_pi(args, scope, fam, env) do
    {domains, [ret]} = Enum.split(args, length(args) - 1)

    with {:ok, dom_cores} <- map_idx_to_core(domains, scope, fam, env),
         {:ok, ret_core} <- idx_to_core(ret, scope, fam, env) do
      pi =
        dom_cores
        |> Enum.with_index()
        |> Enum.reverse()
        |> Enum.reduce(Cure.Core.Term.shift(ret_core, length(dom_cores), 0), fn {dom, i}, acc ->
          {:pi, Cure.Core.Grade.unrestricted(), Cure.Core.Term.shift(dom, i, 0), acc}
        end)

      {:ok, pi}
    end
  end

  defp implicit_global?(env, atom) do
    case Env.get_def(env, atom) do
      %{plicities: p, quantities: q} when is_list(p) and is_list(q) -> :implicit in p or :erased in q
      %{plicities: p} when is_list(p) -> :implicit in p
      %{quantities: q} when is_list(q) -> :erased in q
      _ -> false
    end
  end

  defp args_contain_lambda?(args), do: Enum.any?(args, &match?({:lambda, _, _}, &1))

  # The head resolves to a term-level DEFINITION (carries a `:quantities` list),
  # i.e. `Env.get_def` places it and `elaborate_implicit_app_bidirectional` can
  # peel its Π. Families/ctors have no def quantities and are excluded.
  defp term_level_def?(env, atom) do
    match?(%{quantities: q} when is_list(q), Env.get_def(env, atom))
  end

  defp resolve_index_name(name, env) do
    atom = String.to_atom(name)

    # This runs only in a *type* position (`idx_to_core`), so a name that is both a
    # family and a constructor — a record, whose constructor shares the family name
    # — resolves to the family. A name that is only a constructor (a nullary value
    # like `Z` used as an index argument) still resolves to the constructor.
    cond do
      Env.primitive(env, name) != nil ->
        Env.primitive(env, name)

      # Local wins. The cascade below asks "which table holds this name?", but
      # `Env.resolve_key/3` will reach through a cross-module alias index to
      # answer for a bare name, so the family step can be satisfied by a family
      # this module merely IMPORTED while the module's own declaration of that
      # name — a typealias, which lives in `env.defs` — sits one step lower.
      # Table order is for disambiguating declarations within a single scope (a
      # record's family over its same-named constructor); deciding between scopes
      # is a separate question, and answering it with table order hands imports
      # precedence over the local declaration.
      #
      # `@prelude @builtin(:char) opaque type Char` made this visible: it is a
      # family ambient in every module, so a module writing its own
      # `typealias Char = …` got `Std.Char#Char` in every annotation instead —
      # silently, since both spellings name a type.
      owned_typealias(env, atom) != nil ->
        owned_typealias(env, atom)

      Inductive.family?(env, atom) ->
        {:data, Env.resolve_key(env, env.families, atom), [], []}

      # Transparent type aliases are stored as type-level definitions rather
      # than inductive families. In a type position they must win over a
      # same-spelled value constructor just as a family does. Without this,
      # declaring `Value.String(String)` made the second `String` (and every
      # later field annotation named `String`) resolve to the freshly declared
      # constructor, eventually leaking a bare kernel `:ctor_arity` failure.
      # Ordinary term definitions remain usable in dependent indices through
      # this same global form; the kernel checks that the selected definition is
      # actually well-sorted for its position.
      Env.get_def(env, atom) != nil ->
        {:global, Env.resolve_key(env, env.defs, atom)}

      Inductive.get_ctor(env, atom) ->
        {:ctor, Env.resolve_key(env, env.ctors, atom), []}

      # A bare name reachable only under a single re-keyed `:"Mod#name"` variant
      # (shadowed-but-present, spec §3.3). Exactly-one resolves; ≥2 (ambiguous)
      # falls through to `{:global, atom}` here and is caught by R7 (Task 10).
      match?({:ok, _}, Cure.Elab.Resolution.resolve_bare(env, atom)) ->
        {:ok, key} = Cure.Elab.Resolution.resolve_bare(env, atom)

        cond do
          Inductive.family?(env, key) -> {:data, key, [], []}
          Env.get_def(env, key) -> {:global, key}
          true -> {:ctor, key, []}
        end

      # ≥2 distinct re-keyed origins, no local/unshadowed winner: unqualified use
      # is ambiguous (R7). The caller turns this marker into an error.
      length(Cure.Elab.Resolution.ambiguous_modules(env, atom)) >= 2 ->
        {:ambiguous_name, atom, Cure.Elab.Resolution.ambiguous_modules(env, atom)}

      Cure.Elab.Resolution.retired_type_name?(name) ->
        {:retired_process_type, atom}

      true ->
        {:global, atom}
    end
  end

  # An authored `typealias` the CURRENT module owns, looked up under its
  # owner-qualified key so no alias index can widen the search to another module.
  #
  # Only typealiases, and deliberately so. `env.defs` also holds ordinary term
  # definitions and constructor wrappers, whose place BELOW families in the
  # cascade is load-bearing: `Std.Dynamic` declares `Int(Int)`, so promoting
  # everything a module owns would make the field annotation in
  # `fn of_int(n: Int)` resolve to that constructor and fail in the kernel as
  # `:ctor_arity` — the same leak the branch below already guards against. A
  # typealias is the one entry in `env.defs` that *declares a type name*, which is
  # what makes it a peer of the family it has to win against. `Env.put_typealias/2`
  # sets this marker for exactly that purpose.
  defp owned_typealias(env, atom) do
    owned = Env.owned_name(env, atom)

    case Map.get(env.defs, owned) do
      %{typealias: true} -> {:global, owned}
      _ -> nil
    end
  end

  # `@erases(<class>)` on an opaque carrier. Absent → nil (undeclared, the common
  # case). Present but not admissible → a compile error naming the class, rather than
  # a silently undeclared carrier that fails much later inside union discrimination
  # with an unrelated message.
  defp erasure_class(meta, name) do
    case Keyword.get(meta, :decorator) do
      {:decorator, dm, args} when is_list(dm) ->
        case Keyword.get(dm, :name) do
          :erases -> erases_class(args, name)
          :builtin -> {:ok, builtin_erasure_class(args)}
          _ -> {:ok, nil}
        end

      _ ->
        {:ok, nil}
    end
  end

  # A declaration meta holds ONE decorator slot, so a carrier that must announce a
  # builtin key cannot also spell `@erases(...)`. It does not need to: a builtin key
  # already fixes the runtime shape, because the kernel — not the source — supplies
  # that family's values. `@builtin(:char) opaque type Char` therefore erases to an
  # integer for the same reason its literals are `{:bounded_lit, k}`: a code point is
  # one machine integer. Keys with no constructor-less carrier are unaffected (nil,
  # i.e. undeclared), since erasure for those is inferred from their constructors.
  defp builtin_erasure_class([{:literal, _meta, :char}]), do: :integer
  defp builtin_erasure_class([:char]), do: :integer
  defp builtin_erasure_class(_args), do: nil

  # The class argument of an `@erases(<class>)` decorator, validated against the
  # admissible set. Any other argument shape — zero args, more than one arg, or an
  # argument that isn't an atom literal (e.g. a bare identifier missing its `:`) — is a
  # malformed decorator, not an absent one, and becomes a compile error naming the
  # mistake. Reporting it here (rather than falling through to `{:ok, nil}`) is what
  # stops a typo silently reading as "undeclared", since there is no later checkpoint
  # that would catch it — a `nil` erasure just means "no carrier class declared".
  defp erases_class([{:literal, _, class}], _name) when class in @erasure_classes,
    do: {:ok, class}

  defp erases_class([{:literal, _, class}], name),
    do: {:error, {:unknown_erasure_class, name, class}}

  defp erases_class(other_args, name),
    do: {:error, {:unknown_erasure_class, name, malformed_erases_arg(other_args)}}

  # A short, readable stand-in for the malformed `@erases(...)` argument list, so the
  # `:unknown_erasure_class` message names the actual mistake instead of dumping the
  # raw parser AST (line/col meta and all) at the caller. The single-atom-literal shape
  # is handled by the two clauses above `erasure_class` dispatches through before
  # reaching this fallback, so only the genuinely malformed shapes land here.
  defp malformed_erases_arg([]), do: :missing_argument
  defp malformed_erases_arg([_, _ | _] = args), do: {:too_many_arguments, length(args)}
  defp malformed_erases_arg([_not_a_literal]), do: :not_an_atom_literal

  # `@erases` asserts the runtime shape of a carrier that has NO constructors and so
  # no inferable erasure. A type WITH constructors erases to a bare atom (nullary) or
  # a tagged tuple; a declared class could only ever disagree with that. Checked once
  # at the declaration entry point, so every non-opaque container form is covered.
  defp reject_erases_on_non_opaque({:container, meta, _variants}) do
    case {Keyword.get(meta, :container_type), Keyword.get(meta, :decorator)} do
      {ct, {:decorator, dm, _}} when ct != :opaque and is_list(dm) ->
        if Keyword.get(dm, :name) == :erases,
          do: {:error, {:erases_on_non_opaque, meta |> Keyword.fetch!(:name) |> String.to_atom()}},
          else: :ok

      _ ->
        :ok
    end
  end

  defp reject_erases_on_non_opaque(_decl), do: :ok

  # The `@builtin(:tag)` on a primitive container, or an error if absent.
  defp primitive_builtin_tag(meta) do
    case Keyword.get(meta, :decorator) do
      {:decorator, dm, [{:literal, _, tag}]} when is_atom(tag) ->
        if Keyword.get(dm, :name) == :builtin,
          do: {:ok, tag},
          else: {:error, {:primitive_missing_builtin, Keyword.get(meta, :name)}}

      _ ->
        {:error, {:primitive_missing_builtin, Keyword.get(meta, :name)}}
    end
  end

  # The name of an attached decorator node (`{:decorator, [name: n], args}`) held
  # in a container/def meta `:decorator` slot, or `nil` if absent/non-decorator.
  defp attached_decorator_name({:decorator, m, _args}) when is_list(m), do: Keyword.get(m, :name)
  defp attached_decorator_name(_), do: nil

  # Register a def tagged `@lemma` into the proof-search registry, filed under
  # its conclusion head. No-op for untagged defs or non-data conclusions. The
  # entry's name is OWNER-QUALIFIED (Env.owned_name/2) so ProofSearch's assembled
  # {:global, ...} term matches what ordinary elaboration produces for the same
  # call — see Cure.Elab.ProofSearch.
  defp maybe_register_lemma(env, sig, meta) do
    with :lemma <- attached_decorator_name(Keyword.get(meta, :decorator)),
         head when not is_nil(head) <- conclusion_head(sig.pi) do
      Env.put_lemma(env, head, %{
        name: Env.owned_name(env, sig.name),
        type: sig.pi,
        arity: pi_arity(sig.pi)
      })
    else
      _ -> env
    end
  end

  # The head family atom of a Pi type's ultimate codomain, or nil if the
  # conclusion is not an indexed/parameterised data application.
  def conclusion_head({:pi, _g, _dom, cod}), do: conclusion_head(cod)
  def conclusion_head({:data, name, _params, _indices}), do: name
  def conclusion_head(_), do: nil

  defp pi_arity({:pi, _g, _dom, cod}), do: 1 + pi_arity(cod)
  defp pi_arity(_), do: 0

  # The fixed tag→Core-node table — the ONLY inherent mapping (keyed by builtin
  # tag, not by surface name). Exactly three tags are legal now that `Int` has
  # moved off the primitive floor onto the inductive `Std.Int#Int` family
  # (spec 2026-07-18-inductive-int §3a(i)): `:int` is NOT a valid `@builtin`
  # primitive tag anymore. Without this clause, `confirm_primitive_floor/3`
  # trivially accepts ANY `@builtin(_) primitive Int` declaration — `Env.primitive
  # (env, "Int")` is now `nil` (Int is no longer seeded as a primitive), so the
  # floor-disagreement guard has nothing to disagree with — silently creating an
  # incoherent `{:int_type}`/`{:float_type}`-shaped local binding for `Int` that
  # only fails much later, at codegen, with a cryptic `conversion_failure`
  # against the family type. Rejecting `:int` here at the declaration site closes
  # that hole with a clear, early diagnostic instead.
  defp primitive_tag_node(:float), do: {:ok, {:float_type}}
  defp primitive_tag_node(:binary), do: {:ok, {:binary_type}}
  defp primitive_tag_node(:atom), do: {:ok, {:atom_type}}
  defp primitive_tag_node(other), do: {:error, {:unknown_primitive_tag, other}}

  # A declaration's node must match the seeded floor for that name (consistency
  # contract — mirrors the Bool/Nat seeded-look-alike agreement).
  defp confirm_primitive_floor(env, name, node) do
    case Env.primitive(env, name) do
      nil -> :ok
      ^node -> :ok
      other -> {:error, {:primitive_floor_mismatch, name, node, other}}
    end
  end

  # Threads the ctx to NESTED argument positions (spec §7.3 item 3): in
  # `b(first(p))` the head `b` is a bound var; the implicit-carrying global
  # `first` sits one level down, in an argument position.
  defp map_idx_to_core(exprs, scope, fam, env, ctx \\ nil) do
    Enum.reduce_while(exprs, {:ok, []}, fn e, {:ok, acc} ->
      case idx_to_core(e, scope, fam, env, ctx) do
        {:ok, core} -> {:cont, {:ok, acc ++ [core]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp declare_indexed_at_min_level(env, name, param_tele, index_tele, ctors, level) when level <= @ceiling do
    family = Inductive.family(name, param_tele, index_tele, level)
    env2 = Inductive.declare(env, family, ctors)
    family2 = Inductive.get_family(env2, name)

    with :ok <- Kernel.check_family(env2, family2),
         :ok <- check_all_ctors(env2, family2, ctors),
         :ok <- Inductive.positive?(env2, family2) do
      {:ok, env2}
    else
      {:error, :universe_level} ->
        declare_indexed_at_min_level(env, name, param_tele, index_tele, ctors, level + 1)

      {:error, _} = err ->
        err
    end
  end

  defp declare_indexed_at_min_level(_env, _name, _param_tele, _index_tele, _ctors, _level),
    do: {:error, :universe_ceiling}

  # Opaque (postulate) family: register with the `opaque: true` marker and zero
  # constructors, checking only that the parameter telescope is well-formed
  # (level search on `:universe_level`). There are no constructors, so
  # check_all_ctors / positive? are vacuous and deliberately skipped.
  defp declare_opaque_at_min_level(env, name, param_tele, level, erasure) when level <= @ceiling do
    family = Inductive.opaque_family(name, param_tele, level, erasure)
    env2 = Inductive.declare(env, family, [])

    case Kernel.check_family(env2, Inductive.get_family(env2, name)) do
      :ok ->
        {:ok, env2}

      {:error, :universe_level} ->
        declare_opaque_at_min_level(env, name, param_tele, level + 1, erasure)

      {:error, _} = err ->
        err
    end
  end

  defp declare_opaque_at_min_level(_env, _name, _param_tele, _level, _erasure),
    do: {:error, :universe_ceiling}

  # -- declaration at the least well-formed universe level --------------------

  defp declare_at_min_level(env, name, ctors, level) when level <= @ceiling do
    family = Inductive.family(name, [], [], level)
    env2 = Inductive.declare(env, family, ctors)
    family2 = Inductive.get_family(env2, name)

    with :ok <- Kernel.check_family(env2, family2),
         :ok <- check_all_ctors(env2, family2, ctors),
         :ok <- Inductive.positive?(env2, family2) do
      {:ok, env2}
    else
      {:error, :universe_level} -> declare_at_min_level(env, name, ctors, level + 1)
      {:error, _} = err -> err
    end
  end

  defp declare_at_min_level(_env, _name, _ctors, _level), do: {:error, :universe_ceiling}

  defp check_all_ctors(env, family, ctors) do
    Enum.reduce_while(ctors, :ok, fn ctor, :ok ->
      case Kernel.check_ctor(env, family, ctor) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end
end
