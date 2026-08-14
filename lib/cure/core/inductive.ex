defmodule Cure.Core.Env do
  @moduledoc """
  The global signature: indexed inductive families, their constructors, and
  (from M7.1) global function definitions plus the set of totality-certified
  globals that δ-reduction is permitted to unfold.

  This is the single shared environment threaded through the kernel and
  elaborator; later tasks refer to it as `Core.Env`. It carries no PIDs or
  closures — only Core terms and metadata — so it stays serializable.
  """

  # Where `alias_index/1` memoizes its indexes, and how many table versions it
  # keeps. `resolve_key/3` is called with five tables (`defs`, `families`,
  # `ctors`, `ctor_to_family`, `constrained`); a handful of slots holds their
  # current versions, and the bound is what stops a long elaboration — which
  # produces a new table term on every registration — from retaining every
  # superseded one. Entries are pure derived data, so evicting one only costs a
  # rebuild.
  @alias_index_key {__MODULE__, :alias_index}
  @alias_index_slots 8
  @visible_alias_index_key {__MODULE__, :visible_alias_index}
  @visible_alias_index_slots 16

  defstruct families: %{},
            ctors: %{},
            ctor_to_family: %{},
            defs: %{},
            direct_call_summaries: %{},
            totality_components: %{},
            totality_component_of: %{},
            certified: nil,
            totality_certified: nil,
            builtins: %{},
            interfaces: %{},
            interface_methods: %{},
            coherence: nil,
            constrained: %{},
            primitives: %{},
            import_modules: MapSet.new(),
            bare_modules: nil,
            bare_bindings: nil,
            qualified_modules: nil,
            lemmas: %{},
            equations: %{},
            module_owner: nil,
            current_def: nil

  @type t :: %__MODULE__{
          families: %{atom() => map()},
          ctors: %{atom() => map()},
          ctor_to_family: %{atom() => atom()},
          defs: %{atom() => map()},
          direct_call_summaries: %{atom() => map()},
          totality_components: %{binary() => map()},
          totality_component_of: %{atom() => binary()},
          certified: MapSet.t() | nil,
          totality_certified: MapSet.t() | nil,
          builtins: %{atom() => atom()},
          interfaces: %{atom() => map()},
          interface_methods: %{atom() => map()},
          coherence: term(),
          constrained: %{atom() => [map()]},
          primitives: %{String.t() => tuple()},
          # The source module whose declarations are currently being
          # elaborated. Imported environments retain their own owner until
          # their canonical entries are merged into the importing environment.
          module_owner: String.t() | nil,
          # Inert elaborator metadata (the kernel never reads it): the set of
          # module-ids DIRECTLY imported by the module this env belongs to
          # (explicit `use` + auto-prelude). Bare-name resolution prefers a
          # direct owner over a name reachable only via a module's transitive
          # re-export, matching must-import semantics (Haskell/Elm/Idris/Swift).
          import_modules: MapSet.t(String.t()),
          # Modules whose declarations may be referenced by a bare spelling.
          # `nil` is retained only for ownerless/synthetic compatibility
          # environments; real module elaboration installs an explicit set.
          bare_modules: MapSet.t(String.t()) | nil,
          # Exact canonical declarations exposed by lexical imports, ambient
          # prelude items, and the compiler seed. Unlike `bare_modules`, this
          # can expose `Std.List#List`/`Std.List#Nil` without also exposing
          # every function owned by Std.List.
          bare_bindings: MapSet.t(atom()) | nil,
          # Modules whose canonical declarations may be referenced through an
          # authored qualified path. This is deliberately independent of
          # `import_modules`: `M.f` makes M available without opening `f`.
          qualified_modules: MapSet.t(String.t()) | nil,
          # Inert elaborator metadata (the kernel never reads it): `@lemma`-tagged
          # theorems keyed by their conclusion-head atom, for auto proof-search
          # (see `Cure.Elab.ProofSearch`). Same status as `interfaces`/`coherence`.
          lemmas: %{atom() => [map()]},
          # Inert elaborator metadata describing kernel-checked defining
          # equations. The kernel never consults this index.
          equations: %{atom() => [map()]},
          # Inert elaborator metadata (the kernel never reads it): the name of the
          # def whose body is currently being elaborated, set for the duration of
          # `Declarations.elaborate_real_body/3`. Consumed ONLY by
          # `Declarations.hole_id/2` so a hole id is qualified by
          # `<module>.<def>`, not just `<module>` — two different defs writing the
          # same named hole (`?goal` in `a` and `?goal` in `b`) must mint DISTINCT
          # ids, or `Conv` would judge them definitionally equal (first-class
          # holes soundness pivot).
          current_def: atom() | nil
        }

  @doc "An empty signature."
  @spec empty() :: t()
  def empty, do: %__MODULE__{certified: MapSet.new(), totality_certified: MapSet.new()}

  @doc "Attach the source-module owner used for canonical declaration identity."
  @spec with_owner(t(), String.t() | atom() | nil) :: t()
  def with_owner(%__MODULE__{} = env, nil), do: %{env | module_owner: nil}

  def with_owner(%__MODULE__{} = env, owner) when is_atom(owner),
    do: with_owner(env, Atom.to_string(owner))

  def with_owner(%__MODULE__{} = env, owner) when is_binary(owner) or is_nil(owner),
    do: %{env | module_owner: owner}

  @doc "Return the source-module owner for the current elaboration environment."
  @spec owner(t()) :: String.t() | nil
  def owner(%__MODULE__{module_owner: owner}), do: owner

  @doc "Install the lexical and qualified module visibility for this elaboration."
  @spec with_module_visibility(t(), MapSet.t(String.t()), MapSet.t(String.t())) :: t()
  def with_module_visibility(%__MODULE__{} = env, bare_modules, qualified_modules) do
    %{
      env
      | bare_modules: bare_modules,
        qualified_modules: qualified_modules
    }
  end

  @doc "Whether an owner may supply a bare spelling in this environment."
  @spec bare_module_available?(t(), String.t() | nil) :: boolean()
  def bare_module_available?(%__MODULE__{bare_modules: nil}, _owner), do: true

  def bare_module_available?(%__MODULE__{bare_modules: modules, module_owner: owner}, candidate),
    do: candidate == owner or MapSet.member?(modules, candidate)

  @doc "Whether one canonical declaration may supply a bare spelling."
  @spec bare_key_available?(t(), atom()) :: boolean()
  def bare_key_available?(%__MODULE__{bare_bindings: nil} = env, key),
    do: bare_module_available?(env, Cure.Elab.Name.owner(key))

  def bare_key_available?(%__MODULE__{bare_bindings: bindings, module_owner: owner}, key) do
    Cure.Elab.Name.owner(key) == owner or MapSet.member?(bindings, key)
  end

  @doc "Whether an owner may be named by a qualified surface path."
  @spec qualified_module_available?(t(), String.t() | nil) :: boolean()
  def qualified_module_available?(%__MODULE__{qualified_modules: nil}, _owner), do: true

  def qualified_module_available?(%__MODULE__{qualified_modules: modules, module_owner: owner}, candidate),
    do: candidate == owner or MapSet.member?(modules, candidate)

  @doc """
  Attach the name of the def whose body is currently being elaborated (see the
  `current_def` field doc). Set once per top-level def, at the single entry
  point `Declarations.elaborate_real_body/3`, before body elaboration begins.
  """
  @spec with_current_def(t(), atom() | nil) :: t()
  def with_current_def(%__MODULE__{} = env, name), do: %{env | current_def: name}

  @doc "The name of the def currently being elaborated, or `nil` outside one."
  @spec current_def(t()) :: atom() | nil
  def current_def(%__MODULE__{current_def: name}), do: name

  @doc """
  Register a global function definition (declared type + Core body). The kernel
  must `check_def/2` it before it may be referenced; certification (M7.2) gates
  whether δ-reduction may unfold it.
  """
  @typedoc """
  What a definition's body slot may actually hold.

  Three inhabitants, and only the first is a Core term:

    * a `Cure.Core.Term.t()` — an ordinary definition;
    * `nil` — a builtin, seeded with a type but no body (`Cure.Core.Builtins`);
    * `{:extern, {mod, fun, arity}}` — an `@extern` FFI binding, whose body lives
      on the BEAM, not in Core.

  The spec used to claim this was always a term. Dialyzer disagreed, and it was
  right: `Declarations` passes the `:extern` tuple and `Builtins` passes `nil`.
  """
  @type def_body :: Cure.Core.Term.t() | nil | {:extern, {module(), atom(), arity()}}

  @spec add_def(t(), atom(), Cure.Core.Term.t(), def_body()) :: t()
  def add_def(env, name, type_term, body_term), do: add_def(env, name, type_term, body_term, nil, nil)

  @doc """
  Register a global function definition with per-parameter {0,ω} quantities
  (`nil` = unspecified/all runtime-relevant). Erased parameters are dropped by
  erasure (M8.3 / M9).
  """
  @spec add_def(t(), atom(), Cure.Core.Term.t(), def_body(), [atom()] | nil) :: t()
  def add_def(env, name, type_term, body_term, quantities),
    do: add_def(env, name, type_term, body_term, quantities, nil)

  def add_def(%__MODULE__{} = env, name, type_term, body_term, quantities, plicities) do
    name = owned_name(env, name)

    preserve_sealed? =
      body_term == {:hole, "__pending__"} and total?(env, name)

    {certified, totality_certified, components, component_of} =
      if preserve_sealed? do
        {env.certified, env.totality_certified, env.totality_components, env.totality_component_of}
      else
        invalidate_totality_component(env, name)
      end

    summaries =
      if preserve_sealed?,
        do: env.direct_call_summaries,
        else: Map.delete(env.direct_call_summaries, name)

    %{
      env
      | defs:
          Map.put(env.defs, name, %{
            name: name,
            type: type_term,
            body: body_term,
            quantities: quantities,
            plicities: plicities
          }),
        direct_call_summaries: summaries,
        totality_components: components,
        totality_component_of: component_of,
        certified: certified,
        totality_certified: totality_certified
    }
  end

  defp invalidate_totality_component(env, name) do
    case Map.get(env.totality_component_of, name) do
      nil ->
        certified = if is_nil(env.certified), do: nil, else: MapSet.delete(env.certified, name)
        totality = if is_nil(env.totality_certified), do: nil, else: MapSet.delete(env.totality_certified, name)
        {certified, totality, env.totality_components, env.totality_component_of}

      digest ->
        members = get_in(env.totality_components, [digest, :members]) || [name]
        member_set = MapSet.new(members)
        certified = if is_nil(env.certified), do: nil, else: MapSet.difference(env.certified, member_set)

        totality =
          if is_nil(env.totality_certified), do: nil, else: MapSet.difference(env.totality_certified, member_set)

        {certified, totality, Map.delete(env.totality_components, digest), Map.drop(env.totality_component_of, members)}
    end
  end

  @doc "Store the trusted direct-call summary for a checked definition."
  @spec put_direct_call_summary(t(), atom(), map()) :: t()
  def put_direct_call_summary(%__MODULE__{} = env, name, summary) when is_map(summary) do
    key = resolve_key(env, env.defs, name)
    %{env | direct_call_summaries: Map.put(env.direct_call_summaries, key, summary)}
  end

  @doc "Return the cached direct-call summary for a canonical definition, if any."
  @spec direct_call_summary(t(), atom()) :: map() | nil
  def direct_call_summary(%__MODULE__{} = env, name) do
    Map.get(env.direct_call_summaries, resolve_key(env, env.defs, name))
  end

  @doc "Atomically publish a kernel-verified totality result for an SCC."
  @spec certify_component(t(), [atom()], binary()) :: t()
  def certify_component(%__MODULE__{} = env, members, digest)
      when is_list(members) and is_binary(digest) do
    members = Enum.sort(members)
    certified = Enum.reduce(members, env, &certify(&2, &1))

    %{
      certified
      | totality_components: Map.put(certified.totality_components, digest, %{members: members, digest: digest}),
        totality_component_of: Enum.reduce(members, certified.totality_component_of, &Map.put(&2, &1, digest))
    }
  end

  @doc "Mark a registered definition as requiring the explicit `unsafe` call marker."
  @spec put_unsafe(t(), atom(), boolean()) :: t()
  def put_unsafe(%__MODULE__{} = env, name, required \\ true) when is_boolean(required) do
    key = resolve_key(env, env.defs, name)

    case Map.fetch(env.defs, key) do
      {:ok, definition} -> %{env | defs: Map.put(env.defs, key, Map.put(definition, :unsafe, required))}
      :error -> env
    end
  end

  @doc """
  Mark a registered definition as reducible across the module boundary — its body
  is published in the canonical interface so consumers may δ-unfold it.

  Signature visibility and reducibility are separate decisions (Idris 2's
  `export` vs `public export`). A consumer that states a theorem *about* a
  provider's function needs that function to compute, and no provider-local
  analysis can predict which of its definitions some future consumer will
  reason about — so the author says. Unmarked bodies stay opaque, which is what
  keeps a module's interface hash insensitive to ordinary body edits.
  """
  @spec put_reducible(t(), atom(), boolean()) :: t()
  def put_reducible(%__MODULE__{} = env, name, reducible \\ true) when is_boolean(reducible) do
    key = resolve_key(env, env.defs, name)

    case Map.fetch(env.defs, key) do
      {:ok, definition} -> %{env | defs: Map.put(env.defs, key, Map.put(definition, :reducible, reducible))}
      :error -> env
    end
  end

  @doc "Attach inert authored-hole metadata to a definition for release-boundary diagnostics."
  @spec put_source_holes(t(), atom(), map()) :: t()
  def put_source_holes(%__MODULE__{} = env, name, source_holes) when is_map(source_holes) do
    key = resolve_key(env, env.defs, name)

    case Map.fetch(env.defs, key) do
      {:ok, definition} -> %{env | defs: Map.put(env.defs, key, Map.put(definition, :source_holes, source_holes))}
      :error -> env
    end
  end

  @doc "The global definition `%{name, type, body}` for `name`, or nil."
  @spec get_def(t(), atom()) :: map() | nil
  def get_def(%__MODULE__{} = env, name), do: Map.get(env.defs, resolve_key(env, env.defs, name))

  @doc "Mark a definition as an authored transparent type alias."
  @spec put_typealias(t(), atom()) :: t()
  def put_typealias(%__MODULE__{} = env, name) do
    key = resolve_key(env, env.defs, name)

    case Map.fetch(env.defs, key) do
      {:ok, definition} -> %{env | defs: Map.put(env.defs, key, Map.put(definition, :typealias, true))}
      :error -> env
    end
  end

  @doc "Return the owner-qualified key for a declaration in the current module."
  @spec owned_name(t(), atom() | String.t()) :: atom()
  def owned_name(%__MODULE__{module_owner: owner}, name) when is_binary(name),
    do: owned_name(%__MODULE__{module_owner: owner}, String.to_atom(name))

  def owned_name(%__MODULE__{module_owner: nil}, name), do: name

  def owned_name(%__MODULE__{module_owner: owner}, name) when is_atom(name) do
    if Cure.Elab.Name.qualified?(name), do: name, else: Cure.Elab.Name.qualify(owner, name)
  end

  @doc "Resolve a bare key against the current module's canonical key first."
  @spec resolve_key(t(), map(), atom() | String.t()) :: atom()
  def resolve_key(%__MODULE__{} = env, table, name) when is_binary(name),
    do: resolve_key(env, table, String.to_atom(name))

  def resolve_key(%__MODULE__{} = env, table, name) when is_atom(name) do
    owned = owned_name(env, name)

    cond do
      Map.has_key?(table, owned) ->
        owned

      Map.has_key?(table, name) ->
        name

      true ->
        # Last resort: the name is bare and unowned, so find the unique
        # owner-qualified key whose base it is — via an index, because
        # rediscovering it by walking every key made this O(table) on every
        # unresolved lookup.
        candidates =
          resolution_name_indexes(env, table).aliases
          |> Map.get(Atom.to_string(name), [])
          |> Enum.filter(&bare_key_available?(env, &1))

        case candidates do
          [key] -> key
          _ -> name
        end
    end
  end

  # Real source modules carry an exact lexical `bare_bindings` set. Unlike the
  # definition tables, that set is stable while function bodies replace pending
  # definitions with checked bodies. Index it directly so every new `defs` map
  # does not force another walk over hundreds of unchanged imported names.
  defp resolution_name_indexes(%__MODULE__{bare_bindings: %MapSet{} = bindings} = env, table) do
    namespace = table_namespace(env, table)
    owner = env.module_owner
    cache = Process.get(@visible_alias_index_key, [])

    case cached_visible_index(cache, bindings, namespace, owner) do
      nil ->
        visible =
          table
          |> Map.keys()
          |> Enum.filter(fn key ->
            MapSet.member?(bindings, key) or
              (is_binary(owner) and Cure.Elab.Name.owner(key) == owner)
          end)
          |> build_name_indexes_from_keys()

        Process.put(
          @visible_alias_index_key,
          Enum.take([{bindings, namespace, owner, visible} | cache], @visible_alias_index_slots)
        )

        visible

      index ->
        index
    end
  end

  defp resolution_name_indexes(_env, table), do: name_indexes(table)

  defp table_namespace(env, table) do
    cond do
      :erts_debug.same(table, env.defs) -> :defs
      :erts_debug.same(table, env.families) -> :families
      :erts_debug.same(table, env.ctors) -> :ctors
      :erts_debug.same(table, env.ctor_to_family) -> :ctor_to_family
      :erts_debug.same(table, env.constrained) -> :constrained
      true -> :other
    end
  end

  defp cached_visible_index([], _bindings, _namespace, _owner), do: nil

  defp cached_visible_index(
         [{cached, namespace, owner, index} | rest],
         bindings,
         namespace,
         owner
       ) do
    if :erts_debug.same(cached, bindings),
      do: index,
      else: cached_visible_index(rest, bindings, namespace, owner)
  end

  defp cached_visible_index([_other | rest], bindings, namespace, owner),
    do: cached_visible_index(rest, bindings, namespace, owner)

  # base => [owner-qualified keys with that base], for `resolve_key/3`'s fallback.
  #
  # The index is a pure function of the table's KEY SET, so it is cached under
  # the table value itself rather than maintained at the (scattered) sites that
  # write `defs`/`families`/`ctors`. That choice is what makes a stale read
  # impossible: a table whose keys changed is a different term, so it misses the
  # cache and the index is rebuilt. A hit means the terms compare equal, which
  # means the key sets are equal, which means the index describes this table.
  # There is no invariant for a future writer to maintain, and nothing to drift.
  #
  # Lookup compares with `:erts_debug.same/2` — physical identity, O(1) — rather
  # than `===`, which would deep-compare these nested def maps whenever the
  # pointers differ and could cost more than the walk it replaces. Identity is
  # only ever a conservative approximation of equality: two structurally equal
  # tables at different addresses simply miss and rebuild, which is correct and
  # costs the same O(table) walk the fallback used to pay unconditionally. So
  # this is never the slower choice, and never the wrong one.
  defp name_indexes(table) do
    cache = Process.get(@alias_index_key, [])

    case cached_index(cache, table) do
      nil ->
        index = build_name_indexes(table)
        Process.put(@alias_index_key, Enum.take([{table, index} | cache], @alias_index_slots))
        index

      index ->
        index
    end
  end

  defp cached_index([], _table), do: nil

  defp cached_index([{cached, index} | rest], table),
    do: if(:erts_debug.same(cached, table), do: index, else: cached_index(rest, table))

  defp build_name_indexes(table) do
    table |> Map.keys() |> build_name_indexes_from_keys()
  end

  defp build_name_indexes_from_keys(keys) do
    Enum.reduce(keys, %{aliases: %{}, providers: %{}}, fn key, indexes ->
      case owned_base(key) do
        nil ->
          put_provider(indexes, key)

        base ->
          indexes
          |> Map.update!(:aliases, &Map.update(&1, base, [key], fn keys -> [key | keys] end))
          |> put_provider(key)
      end
    end)
  end

  defp put_provider(indexes, key) when is_atom(key) do
    base = Cure.Elab.Name.overload_base(key)
    Map.update!(indexes, :providers, &Map.update(&1, base, [key], fn keys -> [key | keys] end))
  end

  defp put_provider(indexes, _key), do: indexes

  @doc "Return canonical and overload keys supplied by a bare spelling."
  @spec provider_keys(map(), atom() | String.t()) :: [atom()]
  def provider_keys(table, bare) when is_atom(bare), do: provider_keys(table, Atom.to_string(bare))

  def provider_keys(table, bare) when is_map(table) and is_binary(bare) do
    Map.get(name_indexes(table).providers, bare, [])
  end

  # The base of an owner-qualified key, or nil for anything else. Non-atom keys
  # are not owner-qualified names and are skipped.
  defp owned_base(key) when is_atom(key) do
    case Cure.Elab.Name.split(key) do
      {nil, _base} -> nil
      {_owner, base} -> base
    end
  end

  defp owned_base(_key), do: nil

  @doc "Register a primitive base type: surface name → its Core type node."
  @spec put_primitive(t(), String.t(), tuple()) :: t()
  def put_primitive(%__MODULE__{primitives: p} = env, name, node) when is_binary(name),
    do: %{env | primitives: Map.put(p, name, node)}

  @doc "The Core node a primitive surface name resolves to, or nil."
  @spec primitive(t(), String.t()) :: tuple() | nil
  def primitive(%__MODULE__{primitives: p}, name) when is_binary(name), do: Map.get(p, name)

  @doc """
  Register a compile-time interface (typeclass) descriptor under its name
  atom. The descriptor is elaborator-level metadata (head var, head kind,
  method field types, default bodies) — see `Cure.Elab.Interface`.
  """
  @spec put_interface(t(), atom(), map()) :: t()
  def put_interface(%__MODULE__{interfaces: ifaces} = env, name, desc),
    do: with_interfaces(env, Map.put(ifaces, name, desc))

  @doc false
  @spec with_interfaces(t(), %{atom() => map()}) :: t()
  def with_interfaces(%__MODULE__{} = env, interfaces) when is_map(interfaces) do
    methods =
      Enum.reduce(interfaces, %{}, fn {_name, descriptor}, index ->
        Enum.reduce(descriptor.methods, index, fn {method, _method_descriptor}, index ->
          Map.put(index, method, descriptor)
        end)
      end)

    %{env | interfaces: interfaces, interface_methods: methods}
  end

  @doc "The interface descriptor for `name`, or nil."
  @spec get_interface(t(), atom()) :: map() | nil
  def get_interface(%__MODULE__{interfaces: ifaces}, name), do: Map.get(ifaces, name)

  @doc """
  Register a `@lemma`-tagged theorem for auto proof-search, filed under the
  head atom of its conclusion type. Inert elaborator metadata — the kernel
  never reads it (like `interfaces`/`coherence`). See `Cure.Elab.ProofSearch`.
  """
  @spec put_lemma(t(), atom(), map()) :: t()
  def put_lemma(%__MODULE__{lemmas: ls} = env, head, entry) when is_atom(head),
    do: %{env | lemmas: Map.update(ls, head, [entry], &(&1 ++ [entry]))}

  @doc "The `@lemma` entries filed under conclusion head `head`, or `[]`."
  @spec lemmas(t(), atom()) :: [map()]
  def lemmas(%__MODULE__{lemmas: ls}, head) when is_atom(head), do: Map.get(ls, head, [])

  @doc "Register a certified defining-equation descriptor for its owner."
  @spec put_equation(t(), atom(), map()) :: t()
  def put_equation(%__MODULE__{equations: equations} = env, owner, descriptor),
    do: %{env | equations: Map.update(equations, owner, [descriptor], &(&1 ++ [descriptor]))}

  @doc "Return the defining equations registered for a function owner."
  @spec equations(t(), atom()) :: [map()]
  def equations(%__MODULE__{} = env, owner) do
    key = resolve_key(env, env.defs, owner)
    Map.get(env.equations, key, [])
  end

  @doc "Replace the coherence registry (instance table) carried in the env."
  @spec put_coherence(t(), term()) :: t()
  def put_coherence(%__MODULE__{} = env, registry), do: %{env | coherence: registry}

  @doc "The coherence registry (instance table), or nil if none set."
  @spec coherence(t()) :: term()
  def coherence(%__MODULE__{coherence: registry}), do: registry

  @doc """
  Record that global `name` carries interface constraints — a list of
  `%{iface, tyvar, head_arg_index, head_arg_type, return_type, dict_name}`
  descriptors, one per
  `requires Iface(a)` clause. A concrete call to a constrained global supplies
  the resolved dictionary as a trailing argument (`Cure.Elab.Resolve`). A nil
  `head_arg_index` means the expected result type determines the head.
  """
  @spec put_constrained(t(), atom(), [map()]) :: t()
  def put_constrained(%__MODULE__{constrained: c} = env, name, specs),
    do: %{env | constrained: Map.put(c, owned_name(env, name), specs)}

  @doc "The interface-constraint descriptors for global `name`, or nil."
  @spec constrained(t(), atom()) :: [map()] | nil
  def constrained(%__MODULE__{} = env, name), do: Map.get(env.constrained, resolve_key(env, env.constrained, name))

  @doc """
  Attach a parameter-label vector to an already-registered global (Ph2 argument
  labels). The vector is telescope-aligned (one entry per binder, in order),
  each a written external label string or `nil` for an unlabelled binder. A
  `nil` vector means the def has no labels at all — it is stored under no key, so
  a label-free def's record stays byte-identical (inertness). The label rides IN
  the `env.defs` record, so it travels with the discriminated overload key.
  """
  @spec put_labels(t(), atom(), [String.t() | nil] | nil) :: t()
  def put_labels(%__MODULE__{} = env, _name, nil), do: env

  def put_labels(%__MODULE__{} = env, name, labels) do
    key = owned_name(env, name)

    case Map.get(env.defs, key) do
      nil -> env
      record -> %{env | defs: Map.put(env.defs, key, Map.put(record, :labels, labels))}
    end
  end

  @doc "The telescope-aligned parameter-label vector for global `name`, or nil."
  @spec labels(t(), atom()) :: [String.t() | nil] | nil
  def labels(%__MODULE__{} = env, name) do
    case get_def(env, name) do
      %{labels: ls} -> ls
      _ -> nil
    end
  end

  @doc """
  Mark a global as totality-certified (δ may unfold it). See M7.2.

  Refuses a def whose body is not closed: δ evaluates a certified body in the
  empty environment, so an open body's free variables would alias context
  variables (a capture). Certification is only legitimately produced by the
  kernel's `validate_certificate` on a checked (hence closed) body; this
  assertion makes an open-bodied certificate impossible to create through the
  public seam. (A5)
  """
  @spec certify(t(), atom()) :: t()
  def certify(%__MODULE__{certified: c, totality_certified: t} = env, name) do
    name = resolve_key(env, env.defs, name)

    case get_def(env, name) do
      %{body: body} ->
        unless Cure.Core.Term.closed?(body) do
          raise ArgumentError,
                "cannot certify #{inspect(name)}: body has a free de Bruijn variable " <>
                  "(open body). Certification requires a closed, kernel-validated body (M7.2 / A5)."
        end

      _ ->
        :ok
    end

    %{
      env
      | certified: MapSet.put(c || MapSet.new(), name),
        totality_certified: MapSet.put(t || MapSet.new(), name)
    }
  end

  @doc "Is the global `name` certified total (δ-reducible)?"
  @spec certified?(t(), atom()) :: boolean()
  def certified?(%__MODULE__{} = env, name), do: MapSet.member?(env.certified, resolve_key(env, env.defs, name))

  @doc "Is `name` kernel-certified total, independently of whether its body is available for δ-unfolding?"
  @spec total?(t(), atom()) :: boolean()
  def total?(%__MODULE__{} = env, name) do
    MapSet.member?(env.totality_certified || MapSet.new(), resolve_key(env, env.defs, name))
  end

  @doc """
  Mark an already-registered global def as a builtin arithmetic/comparison op,
  keyed by the stable op atom (`:add`, `:lt`, …). The marker lives ON the def
  record; every consumer (the Normalise compute hook, emit inline, GuardLint's
  Z3 translation) resolves through it, never through a bare global name — so a
  user def named `int_add` (whose `add_def` overwrites the whole record and
  carries NO marker) is never builtin-folded/inlined/translated (K2, R1).
  Only `Builtins.seed_ops` produces this marker.
  """
  @spec register_builtin_op(t(), atom(), atom()) :: t()
  def register_builtin_op(%__MODULE__{defs: defs} = env, name, op_key),
    do: %{env | defs: Map.update!(defs, resolve_key(env, defs, name), &Map.put(&1, :builtin_op, op_key))}

  @doc """
  The builtin-op key for `name` (`:add`, `:lt`, …), or nil. Tolerates a nil
  signature (GuardLint may hold `Context.signature/1` = nil) — returns nil.
  """
  @spec builtin_op(t() | nil, atom()) :: atom() | nil
  def builtin_op(nil, _name), do: nil

  def builtin_op(%__MODULE__{} = env, name) do
    case get_def(env, name) do
      %{builtin_op: op} -> op
      _ -> nil
    end
  end

  @doc """
  Mark an already-registered global def as an emit-inline candidate (the
  `Std.Bool` connectives and `Std.Sigma` projections), keyed by the stable
  inline atom (`:and`, `:eq`, `:sigma_first`, …). Same R1 discipline as
  `register_builtin_op/3`: the marker lives ON the def record, so a local def
  shadowing the bare name carries no marker and is never inlined, while a
  re-keyed `Mod#name` import keeps its marker and keeps inlining. Only the
  `Std.Bool`/`Std.Sigma` import path produces this marker.
  """
  @spec register_inline_hint(t(), atom(), atom()) :: t()
  def register_inline_hint(%__MODULE__{defs: defs} = env, name, key),
    do: %{env | defs: Map.update!(defs, resolve_key(env, defs, name), &Map.put(&1, :inline_hint, key))}

  @doc """
  The emit-inline key for `name` (`:and`, `:sigma_first`, …), or nil.
  """
  @spec inline_hint(t() | nil, atom()) :: atom() | nil
  def inline_hint(nil, _name), do: nil

  def inline_hint(%__MODULE__{} = env, name) do
    case get_def(env, name) do
      %{inline_hint: key} -> key
      _ -> nil
    end
  end
end

defmodule Cure.Core.Inductive do
  alias Cure.Core.Grade

  @moduledoc """
  Representation of indexed inductive families and their constructors
  (design spec §4.4; mirrors Idris `Core/Context/Data.idr` and Lean
  `inductive.cpp`).

  A **family** has a parameter telescope, an index telescope, and a universe
  level. A **constructor** has an argument telescope and a list of *result
  index terms* — the indices of the family value it builds, written over the
  constructor's parameters and arguments (so they may be computed, e.g.
  `and(d1, d2)`). A telescope is `[{var_name, type_term}]`.

  Well-formedness checking (M3.2), strict positivity (M3.3), and constructor
  application typing (M3.4) build on this representation.
  """

  alias Cure.Core.Env

  @type telescope :: [{atom(), Cure.Core.Term.t()}]
  @typedoc """
  A definition's or constructor's per-argument quantity. This is the **grade
  carrier** (`Cure.Core.Grade.t/0`), not a bespoke pair: `:erased` is `0`, and
  the other three inhabitants all denote a runtime-present argument.
  """
  @type quantity :: Grade.t()
  @type family :: %{
          :name => atom(),
          :params => telescope(),
          :indices => telescope(),
          :level => non_neg_integer(),
          # Set (to `true`) only by `opaque_family/3` for postulate families the
          # kernel refuses to eliminate; absent on ordinary inductive families.
          optional(:opaque) => boolean()
        }
  @typedoc """
  A constructor argument's **plicity** — whether it is supplied *positionally*
  (`:explicit`, written at application and bound positionally in a pattern) or
  *implicitly* (`:implicit`, solved by unification at application and bound by
  name in a pattern). Plicity is orthogonal to `quantity` (`Cure.Core.Grade`):
  an inferred index is `:implicit` + `:erased`, an ordinary field is `:explicit`
  + `:unrestricted`, and a *relevant implicit* (Idris `{k : Nat}`) is `:implicit`
  + `:unrestricted`. The kernel type-checker never reads plicity — it is
  elaboration metadata (argument insertion / pattern binding) riding on the ctor
  record — so it stays outside the soundness core.
  """
  @type plicity :: :implicit | :explicit
  @type ctor :: %{
          name: atom(),
          args: telescope(),
          result_indices: [Cure.Core.Term.t()],
          result_params: [Cure.Core.Term.t()],
          quantities: [quantity()],
          plicities: [plicity()]
        }

  @doc """
  Bind a builtin key to a family-id. Re-binding the key to the SAME family-id is
  an idempotent no-op (the auto-seed + a prelude source's own self-registration
  both target the same canonical family); re-binding to a DIFFERENT family-id is
  a hard error (the single-registration invariant that stops a user module from
  hijacking a builtin key).
  """
  @spec register_builtin(Env.t(), atom(), atom()) :: Env.t()
  def register_builtin(%Env{builtins: b} = env, key, family_id) when is_map_key(b, key) do
    family_id = Env.resolve_key(env, env.families, family_id)

    case Map.fetch!(b, key) do
      ^family_id ->
        env

      other ->
        raise ArgumentError,
              "builtin key #{inspect(key)} already bound to #{inspect(other)} (cannot rebind to #{inspect(family_id)})"
    end
  end

  def register_builtin(%Env{} = env, key, family_id) do
    family_id = Env.resolve_key(env, env.families, family_id)
    %{env | builtins: Map.put(env.builtins, key, family_id)}
  end

  @doc "Resolve a builtin key to its family-id, or nil."
  @spec builtin(Env.t(), atom()) :: atom() | nil
  def builtin(%Env{builtins: b}, key), do: Map.get(b, key)

  @doc "Build a family signature (no registration; see `declare/3`)."
  @spec family(atom(), telescope(), telescope(), non_neg_integer()) :: family()
  def family(name, param_tele, index_tele, level),
    do: %{name: name, params: param_tele, indices: index_tele, level: level}

  @doc """
  Build an OPAQUE (postulate) family signature: constructor-less and marked
  `opaque: true` so the kernel refuses to eliminate it (Agda `postulate T :
  Set`). Distinct from a genuinely-empty inductive — which is unmarked and
  remains ex-falso-eliminable. An opaque type carries values (e.g. `@extern`
  BEAM ops) through the TCB to codegen without the kernel ever inspecting or
  unfolding them. Always parameter-only (no indices).

  `erasure` is the runtime class its values take on the BEAM — declared by
  `@erases(<class>)`, since a family with NO constructors has no erasure to infer.
  `nil` means undeclared, which is what every opaque type that never crosses an
  anonymous union wants. The kernel never reads it; it is elaborator metadata riding
  on the family record.
  """
  @spec opaque_family(atom(), telescope(), non_neg_integer(), atom() | nil) :: family()
  def opaque_family(name, param_tele, level, erasure \\ nil),
    do: %{
      name: name,
      params: param_tele,
      indices: [],
      level: level,
      opaque: true,
      erasure: erasure
    }

  @doc """
  Build a constructor signature. Every argument defaults to runtime-relevant
  (`:unrestricted`, quantity ω); use `ctor/4` to mark inferred index arguments
  `:erased` (quantity 0) so they are dropped by erasure (M8.3 / M9).
  """
  @spec ctor(atom(), telescope(), [Cure.Core.Term.t()]) :: ctor()
  def ctor(name, arg_tele, result_indices),
    do: ctor(name, arg_tele, result_indices, List.duplicate(:unrestricted, length(arg_tele)))

  @doc "Build a constructor signature with explicit {0,ω} argument quantities."
  @spec ctor(atom(), telescope(), [Cure.Core.Term.t()], [quantity()]) :: ctor()
  def ctor(name, arg_tele, result_indices, quantities),
    do: ctor(name, arg_tele, result_indices, quantities, [])

  @doc """
  Build a constructor signature carrying its result *parameter* terms (the
  uniform parameter prefix of the family value it builds) separately from its
  result *index* terms. The parameter-free forms (`ctor/3`, `ctor/4`) default
  `result_params` to `[]`.
  """
  @spec ctor(atom(), telescope(), [Cure.Core.Term.t()], [quantity()], [Cure.Core.Term.t()]) ::
          ctor()
  def ctor(name, arg_tele, result_indices, quantities, result_params),
    do: ctor(name, arg_tele, result_indices, quantities, result_params, derive_plicities(quantities))

  @doc """
  Build a constructor signature carrying explicit per-argument **plicities**
  (`:implicit`/`:explicit`) alongside quantities. The `ctor/5` form derives
  plicity from quantity (`:erased` ⇒ `:implicit`, else `:explicit`), reproducing
  the pre-plicity behavior where every erased argument was an inferred index and
  every runtime-relevant argument was positional. Only a *relevant implicit*
  (`:implicit` + `:unrestricted`, Idris `{k : Nat}`) needs the explicit form.
  """
  @spec ctor(
          atom(),
          telescope(),
          [Cure.Core.Term.t()],
          [quantity()],
          [Cure.Core.Term.t()],
          [plicity()]
        ) :: ctor()
  def ctor(name, arg_tele, result_indices, quantities, result_params, plicities),
    do: %{
      name: name,
      args: arg_tele,
      result_indices: result_indices,
      result_params: result_params,
      quantities: quantities,
      plicities: plicities
    }

  # Back-compat plicity default: an erased argument was always an inferred index
  # (implicit); everything runtime-relevant was positional (explicit).
  defp derive_plicities(quantities),
    do:
      Enum.map(quantities, fn
        :erased -> :implicit
        _ -> :explicit
      end)

  @doc "Register a family and its constructors in the env."
  @spec declare(Env.t(), family(), [ctor()]) :: Env.t()
  def declare(%Env{} = env, %{name: fname} = family, ctors) do
    fname = Env.owned_name(env, fname)

    # Declaration order, recorded once here because it is unrecoverable
    # afterwards: `env.ctors` is a map, so the order constructors arrived in is
    # gone the moment they are stored. See `ctors_of/2`.
    family =
      %{family | name: fname}
      |> Map.put(:ctor_order, Enum.map(ctors, fn %{name: cname} -> Env.owned_name(env, cname) end))

    env = %{env | families: Map.put(env.families, fname, family)}

    Enum.reduce(ctors, env, fn %{name: cname} = c, acc ->
      cname = Env.owned_name(acc, cname)
      c = %{c | name: cname}

      %{
        acc
        | ctors: Map.put(acc.ctors, cname, c),
          ctor_to_family: Map.put(acc.ctor_to_family, cname, fname)
      }
    end)
  end

  # -- accessors --------------------------------------------------------------

  @doc "Is `name` a registered family?"
  @spec family?(Env.t(), atom()) :: boolean()
  def family?(%Env{} = env, name), do: Map.has_key?(env.families, Env.resolve_key(env, env.families, name))

  @doc """
  Is `name` an OPAQUE (postulate) family? The `opaque: true` marker — not the
  constructor count — is what makes a type non-eliminable, so a genuinely-empty
  inductive answers `false` here while `opaque type Effect` answers `true`.
  """
  @spec opaque?(Env.t(), atom()) :: boolean()
  def opaque?(%Env{} = env, name), do: opaque_family?(get_family(env, name))

  @doc "Is `family` (a family map or nil) marked opaque?"
  @spec opaque_family?(family() | nil) :: boolean()
  def opaque_family?(%{opaque: true}), do: true
  def opaque_family?(_), do: false

  @doc "The family signature for `name`, or nil."
  @spec get_family(Env.t(), atom()) :: family() | nil
  def get_family(%Env{} = env, name), do: Map.get(env.families, Env.resolve_key(env, env.families, name))

  @doc "The constructor signature for `name`, or nil."
  @spec get_ctor(Env.t(), atom()) :: ctor() | nil
  def get_ctor(%Env{} = env, name), do: Map.get(env.ctors, Env.resolve_key(env, env.ctors, name))

  @doc "The family a constructor belongs to."
  @spec ctor_family(Env.t(), atom()) :: atom() | nil
  def ctor_family(%Env{} = env, cname),
    do: Map.get(env.ctor_to_family, Env.resolve_key(env, env.ctor_to_family, cname))

  @doc "A constructor's result index terms."
  @spec ctor_result_indices(Env.t(), atom()) :: [Cure.Core.Term.t()] | nil
  def ctor_result_indices(env, cname) do
    case get_ctor(env, cname) do
      nil -> nil
      %{result_indices: ris} -> ris
    end
  end

  @doc "A constructor's argument telescope."
  @spec arg_telescope(Env.t(), atom()) :: telescope() | nil
  def arg_telescope(env, cname) do
    case get_ctor(env, cname) do
      nil -> nil
      %{args: args} -> args
    end
  end

  @doc """
  A constructor's field count (the length of its argument telescope), or nil when
  the constructor is unknown. This is the single authority for "how many of a
  ctor value's spine slots are FIELDS" — the count both `Eval`'s ι-rule (via the
  branch arity) and `Conv`'s params-on-spine coercion strip down to.
  """
  @spec field_count(Env.t(), atom()) :: non_neg_integer() | nil
  def field_count(env, cname) do
    case arg_telescope(env, cname) do
      tele when is_list(tele) -> length(tele)
      _ -> nil
    end
  end

  @doc "A constructor's per-argument {0,ω} quantities (`:erased` / `:unrestricted`)."
  @spec ctor_quantities(Env.t(), atom()) :: [quantity()] | nil
  def ctor_quantities(env, cname) do
    case get_ctor(env, cname) do
      nil -> nil
      %{quantities: qs} -> qs
      _ -> nil
    end
  end

  @doc """
  A constructor's per-argument **plicities** (`:implicit` / `:explicit`). Older
  ctor records built before the field existed derive it from quantity (`:erased`
  ⇒ `:implicit`), so this is total for every constructor with a telescope.
  """
  @spec ctor_plicities(Env.t(), atom()) :: [plicity()] | nil
  def ctor_plicities(env, cname) do
    case get_ctor(env, cname) do
      %{plicities: ps} when is_list(ps) -> ps
      %{quantities: qs} when is_list(qs) -> derive_plicities(qs)
      _ -> nil
    end
  end

  @doc """
  A constructor's plicity list, defaulting to derived-from-quantity when the
  record predates the field. `arg_tele` is used only for its length when neither
  is present (all-`:explicit`). The single authority elaboration consults to tell
  positional fields from solved-implicit ones.
  """
  @spec plicities_of(ctor()) :: [plicity()]
  def plicities_of(%{plicities: ps}) when is_list(ps), do: ps
  def plicities_of(%{quantities: qs}) when is_list(qs), do: derive_plicities(qs)
  def plicities_of(%{args: tele}), do: List.duplicate(:explicit, length(tele))

  @doc "How many of a constructor's arguments are supplied positionally (`:explicit`)."
  @spec explicit_arity(ctor()) :: non_neg_integer()
  def explicit_arity(ctor), do: Enum.count(plicities_of(ctor), &(&1 == :explicit))

  @doc """
  Align two checked spines of the same constructor.

  Core admits a fully explicit inference spelling and a shorter spelling whose
  leading inferred slots are recovered from the expected indexed family. The
  alignment is deliberately pairwise: when both sides retain an implicit field
  it remains available to dependent conversion and GADT index refinement.
  """
  @spec align_ctor_spines(Env.t() | nil, atom(), [term()], [term()]) ::
          {[term()], [term()]}
  def align_ctor_spines(nil, _cname, left, right), do: {left, right}

  def align_ctor_spines(env, cname, left, right) do
    cond do
      length(left) > length(right) and trimmable_ctor_prefix?(env, cname, left, right) ->
        {Enum.drop(left, length(left) - length(right)), right}

      length(right) > length(left) and trimmable_ctor_prefix?(env, cname, right, left) ->
        {left, Enum.drop(right, length(right) - length(left))}

      true ->
        {left, right}
    end
  end

  defp trimmable_ctor_prefix?(env, cname, longer, shorter) do
    case get_ctor(env, cname) do
      nil ->
        false

      ctor ->
        plicities = plicities_of(ctor)
        omitted = length(longer) - length(shorter)

        k6_prefix? =
          length(longer) > length(plicities) and length(shorter) == length(plicities)

        inferred_prefix? =
          length(longer) == length(plicities) and
            length(shorter) == explicit_arity(ctor) and
            Enum.all?(Enum.take(plicities, omitted), &(&1 == :implicit))

        omitted > 0 and (k6_prefix? or inferred_prefix?)
    end
  end

  @doc "A family's index telescope."
  @spec index_telescope(Env.t(), atom()) :: telescope() | nil
  def index_telescope(env, fname) do
    case get_family(env, fname) do
      nil -> nil
      %{indices: idx} -> idx
    end
  end

  @doc "A family's parameter telescope."
  @spec param_telescope(Env.t(), atom()) :: telescope() | nil
  def param_telescope(env, fname) do
    case get_family(env, fname) do
      nil -> nil
      %{params: params} -> params
    end
  end

  @doc "A family's parameter arity (0 if none / unknown)."
  @spec param_count(Env.t(), atom()) :: non_neg_integer()
  def param_count(env, fname), do: length(param_telescope(env, fname) || [])

  @doc "A constructor's result *parameter* terms (the param prefix of its result)."
  @spec ctor_result_params(Env.t(), atom()) :: [Cure.Core.Term.t()] | nil
  def ctor_result_params(env, cname) do
    case get_ctor(env, cname) do
      nil -> nil
      %{result_params: rps} -> rps
      _ -> []
    end
  end

  @doc """
  All constructors registered for the family `fname`, in **declaration order**.

  Declaration order is the canonical order for a family's constructors, as it is
  in Agda, Idris and Lean: it fixes the eliminator's argument order, and it is
  the order a reader expects to see them listed back. It is recorded on the
  family at `declare/3` (`:ctor_order`).

  Filtering `env.ctors` instead — as this did — orders by map iteration, which is
  a hash of the constructor keys. That is stable for a given set of names and
  meaningless to a reader, so `type Left = L1 | L2` could suggest "use one of
  `L2`, `L1`" and an anonymous `Int | Bool` could print as `Bool | Int`, with the
  answer changing whenever an unrelated rename shifted the hash. The filter
  remains as the fallback for family records predating the recorded order.
  """
  @spec ctors_of(Env.t(), atom()) :: [ctor()]
  def ctors_of(%Env{} = env, fname) do
    fname = Env.resolve_key(env, env.families, fname)

    case Map.get(env.families, fname) do
      %{ctor_order: [_ | _] = order} ->
        for name <- order, ctor = Map.get(env.ctors, name), do: ctor

      _family ->
        env.ctors
        |> Map.values()
        |> Enum.filter(fn %{name: n} -> Map.get(env.ctor_to_family, n) == fname end)
    end
  end

  # -- strict positivity ------------------------------------------------------

  @doc """
  Strict positivity check (design spec §4.4; mirrors Agda `Positivity.hs` /
  Idris `Positivity.idr`): the family name may appear in a constructor field
  only strictly positively — never to the left of an arrow (a negative /
  contravariant position), which would break the well-foundedness that makes
  the eliminator and totality sound.
  """
  @spec positive?(Env.t(), family()) :: :ok | {:error, {:non_strictly_positive, atom()}}
  def positive?(env, %{name: fname}) do
    Enum.reduce_while(ctors_of(env, fname), :ok, fn %{name: cname, args: args}, :ok ->
      if Enum.all?(args, fn {_n, ty} -> strictly_positive?(env, fname, ty, MapSet.new()) end) do
        {:cont, :ok}
      else
        {:halt, {:error, {:non_strictly_positive, cname}}}
      end
    end)
  end

  # A field type is strictly positive in `fname` when, at every function arrow,
  # `fname` does not occur in the domain — not even hidden behind another
  # declared family's constructor fields (the through-constructor rule) — and
  # the codomain stays strictly positive. Σ is covariant in both components. A
  # field headed by ANOTHER family is checked by expanding that family's
  # constructor fields (`seen` breaks family cycles). When `fname` occurs inside
  # another family's ARGUMENTS (nested positivity — `Node (List Rose)`), the
  # other family's constructor fields are INSTANTIATED with those arguments and
  # re-checked: a strictly-positive parameter (`List`, `Option`) keeps `fname`
  # positive, a negative one (`Neg t = t -> Empty`) drops it left of an arrow and
  # is rejected. An opaque/constructorless carrier has unknowable polarity and is
  # conservatively rejected.
  defp strictly_positive?(env, fname, {:pi, _g, dom, cod}, seen),
    do: not occurs_deep?(env, fname, dom, seen) and strictly_positive?(env, fname, cod, seen)

  # Instantiating a covariant higher-order parameter (Sigma/Tuple's second
  # component is the common case) can expose a beta-redex in a constructor
  # field. Positivity is a property of the normalized type, not its unreduced
  # spelling: `((fn _ => Json) x)` must be recognized as the positive `Json`
  # occurrence rather than rejected as an opaque application.
  defp strictly_positive?(env, fname, {:app, {:lam, _g, _dom, body}, argument}, seen) do
    argument = Cure.Core.Term.shift(argument, 1, 0)

    normalized =
      body
      |> Cure.Core.Term.subst(0, argument)
      |> Cure.Core.Term.shift(-1, 0)

    strictly_positive?(env, fname, normalized, seen)
  end

  # A recursive occurrence of the family itself is strictly positive ONLY when
  # `fname` does not also occur inside its own parameter/index arguments — the
  # same guard the other-family clause below applies. Without it a negative
  # occurrence buried in the family's own arguments (`Bad ((Bad Unit) -> Empty)`)
  # would be admitted, breaking well-foundedness.
  defp strictly_positive?(env, fname, {:data, fname, ps, is}, _seen),
    do: not Enum.any?(ps ++ is, &occurs?(env, fname, &1))

  defp strictly_positive?(env, fname, {:data, other, ps, is}, seen) do
    args = ps ++ is
    fname_in_args = Enum.any?(args, &occurs?(env, fname, &1))

    cond do
      # Re-entering a family already on the expansion stack — a recursive or
      # mutual occurrence. Greatest-fixpoint: accept (its fields are being
      # verified further up the stack). This is what makes a nested self-call
      # like `Lst(Rose(a))` terminate and admit.
      MapSet.member?(seen, other) ->
        true

      # `fname` is not passed into `other`. Only a direct/mutual reference to
      # `fname` inside `other`'s OWN fields could break positivity; expand and
      # check them (parameters stay bound variables — no instantiation needed).
      not fname_in_args ->
        seen2 = MapSet.put(seen, other)

        env
        |> ctors_of(other)
        |> Enum.all?(fn %{args: fields} ->
          Enum.all?(fields, fn {_n, ty} -> strictly_positive?(env, fname, ty, seen2) end)
        end)

      # `fname` flows into `other`'s arguments, but `other` is opaque
      # (postulate) or constructorless: its parameter polarity is unknowable,
      # so no positive certificate can be issued. Reject (soundly incomplete).
      opaque_or_ctorless?(env, other) ->
        false

      # NESTED positivity (Agda `Positivity.hs` / Coq's "check the instantiated
      # constructors" rule): instantiate `other`'s constructor fields with the
      # ACTUAL arguments and require `fname` to remain strictly positive in each.
      # This drops `fname` into exactly the structural slots where `other` uses
      # each parameter — a negative parameter (`Neg t = t -> Empty`) lands
      # `fname` left of an arrow and is rejected; a positive parameter (`List`,
      # `Option`) keeps it positive.
      true ->
        nt =
          length(param_telescope(env, other) || []) + length(index_telescope(env, other) || [])

        if nt == length(args) do
          seen2 = MapSet.put(seen, other)

          env
          |> ctors_of(other)
          |> Enum.all?(fn ctor ->
            ctor
            |> instantiate_fields(nt, args)
            |> Enum.all?(&strictly_positive?(env, fname, &1, seen2))
          end)
        else
          # Argument arity does not match the declared telescope — the term is
          # malformed for this family; cannot align args to binders. Reject.
          false
        end
    end
  end

  # Any other shape: a type-level application (`Neg Bad`), a type-level λ, a
  # `case`, a bare variable, etc. The kernel has no polarity analysis for these
  # heads, so the family occurring inside one CANNOT be certified strictly
  # positive — `Neg := λt. t -> Empty` makes `Neg Bad` a hidden negative
  # occurrence. The only sound answer is: strictly positive iff the family does
  # not occur at all, mirroring the `:data`-other clause's conservatism (a
  # false-open here admits `False`). An occurrence in a genuinely positive but
  # unanalyzable spot is rejected — soundly incomplete, never unsound.
  defp strictly_positive?(env, fname, other, _seen), do: not occurs?(env, fname, other)

  # An opaque (postulate) or constructorless carrier exposes no constructor
  # fields, so the polarity of its parameters cannot be established. Conservative.
  defp opaque_or_ctorless?(env, other),
    do: opaque?(env, other) or ctors_of(env, other) == []

  # Instantiate a constructor's field telescope by substituting the family's
  # `nt` parameter/index binders with the ACTUAL arguments. Parameters are the
  # outermost binders, so at field position `i` the binder for argument `t`
  # (0-indexed, outermost = 0) sits at de Bruijn index `i + (nt - 1 - t)`; the
  # argument is shifted over the `i` preceding-field binders. `Term.subst` is
  # targeted (it does not renumber the untouched binders) — exactly what the
  # positivity predicates, which match `fname` by head and inspect arrow
  # structure (index-insensitive), require.
  defp instantiate_fields(%{args: field_tele}, nt, args) do
    field_tele
    |> Enum.with_index()
    |> Enum.map(fn {{_n, ty}, i} ->
      Enum.reduce(0..(nt - 1)//1, ty, fn t, acc ->
        j = i + (nt - 1 - t)
        Cure.Core.Term.subst(acc, j, Cure.Core.Term.shift(Enum.at(args, t), i, 0))
      end)
    end)
  end

  # Does `fname` occur anywhere in `ty`, including inside the constructor fields
  # of other families referenced by `ty`? Used for arrow DOMAINS, where any
  # reachable occurrence is a negative position.
  defp occurs_deep?(env, fname, ty, seen) do
    occurs?(env, fname, ty) or
      Enum.any?(data_heads(env, ty), fn other ->
        other != fname and not MapSet.member?(seen, other) and
          env
          |> ctors_of(other)
          |> Enum.any?(fn %{args: args} ->
            Enum.any?(args, fn {_n, t} ->
              occurs_deep?(env, fname, t, MapSet.put(seen, other))
            end)
          end)
      end)
  end

  # Every family name appearing as a `{:data, …}` head anywhere in the term,
  # looking THROUGH `{:global, _}` type synonyms — a field written as the bare
  # alias `Wrap` (where `typealias Wrap = W`) must still expose `W` as a head, or
  # `occurs_deep?`'s through-constructor rule never inspects `W`'s fields.
  defp data_heads(env, term),
    do: term |> gather_data_heads(env, MapSet.new(), MapSet.new()) |> MapSet.to_list()

  defp gather_data_heads({:data, n, ps, is}, env, acc, seen),
    do: Enum.reduce(ps ++ is, MapSet.put(acc, n), &gather_data_heads(&1, env, &2, seen))

  defp gather_data_heads({:global, g}, env, acc, seen) do
    if MapSet.member?(seen, g) do
      acc
    else
      case Env.get_def(env, g) do
        %{body: body} when not is_nil(body) ->
          gather_data_heads(body, env, acc, MapSet.put(seen, g))

        _ ->
          acc
      end
    end
  end

  defp gather_data_heads(t, env, acc, seen) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.reduce(acc, &gather_data_heads(&1, env, &2, seen))

  defp gather_data_heads(l, env, acc, seen) when is_list(l),
    do: Enum.reduce(l, acc, &gather_data_heads(&1, env, &2, seen))

  defp gather_data_heads(_t, _env, acc, _seen), do: acc

  # Does the family name `fname` occur anywhere in `term` (as an applied family)?
  #
  # This walker is FAIL-CLOSED: its catch-all descends into any unrecognized
  # tuple/list rather than answering "does not occur". Its callers
  # (`strictly_positive?`, `occurs_deep?`) read `false` as "safe to admit", so a
  # fail-OPEN catch-all here is a soundness hole, not a missing optimization —
  # any Core node shape it failed to enumerate would silently smuggle a negative
  # occurrence past the positivity check. The structural descent makes the
  # enumeration total by construction; it is the same over-approximating pattern
  # `Cure.Core.Kernel.occurs_index?/2` uses. Constructor/family NAMES are atoms,
  # which are leaves, so `fname` is only ever matched against a `{:data, …}` head
  # — never against a name that merely happens to be spelled the same.
  #
  # `{:global, g}` is δ-unfolded before the decision. Agda (`Positivity.hs`),
  # Lean 4 (the `inductive` elaborator) and Idris 2 (`Positivity.idr`) all run
  # the positivity walk over the alias-EXPANDED type, precisely so that
  # `typealias Neg = Bad -> Int` cannot smuggle a negative occurrence of `Bad`
  # into `MkBad : Neg -> Bad` — the classic `MkBad : (Bad -> Nat) -> Bad` paradox
  # constructor, which inhabits `False`.
  #
  # Read the question as: does `fname` occur in `term`'s δ-NORMAL FORM? Then an
  # OPAQUE global (no body, or absent from the signature) normalizes to itself
  # and demonstrably contains no occurrence — `false` is the correct answer, not
  # a fail-open one. This is what keeps `{:app, {:global, :Neg}, Empty}` admitted
  # while `{:app, {:global, :Neg}, Bad}` is still rejected: `Bad` is found in the
  # ARGUMENT by the structural walk, not in the opaque head. On a cyclic global,
  # the first traversal has already inspected the complete finite body syntax;
  # revisiting that same body cannot reveal a previously unseen occurrence.
  defp occurs?(env, fname, term), do: occurs?(env, fname, term, MapSet.new())

  defp occurs?(_env, fname, {:data, fname, _ps, _is}, _seen), do: true

  # Defensive: a family is normally referenced as `{:data, fname, _, _}`, never as
  # a bare global, but if the two name spaces ever collide, treat it as an occurrence.
  defp occurs?(_env, fname, {:global, fname}, _seen), do: true

  defp occurs?(env, fname, {:global, g}, seen) do
    if MapSet.member?(seen, g) do
      # We have already inspected this global's body on the current expansion
      # path. Re-entering it cannot reveal a new syntactic occurrence of
      # `fname`; any such occurrence was visited before the recursive edge.
      # Treating every value-level recursion cycle as an occurrence invents a
      # dependency on the family under review and rejects unrelated constructor
      # fields (notably proof indices containing recursive machine functions).
      false
    else
      case Env.get_def(env, g) do
        %{body: body} when not is_nil(body) -> occurs?(env, fname, body, MapSet.put(seen, g))
        _ -> false
      end
    end
  end

  defp occurs?(env, fname, t, seen) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.any?(&occurs?(env, fname, &1, seen))

  defp occurs?(env, fname, l, seen) when is_list(l),
    do: Enum.any?(l, &occurs?(env, fname, &1, seen))

  defp occurs?(_env, _fname, _leaf, _seen), do: false
end
