defmodule Cure.Audit.Ledger do
  @moduledoc """
  Enumerate what a module assumes without proof.

  Reads the elaborated `Cure.Core.Env`, never source text: a macro may emit an
  `@extern`, and macro output is re-elaborated, so `Core.Env` is the only vantage
  point that observes every axiom. Untrusted; outside the TCB.
  """

  alias Cure.Audit.Refs
  alias Cure.Core.Env
  alias Cure.Core.Printer
  alias Cure.Elab.Program

  defmodule Axiom do
    @moduledoc false
    defstruct [:mfa, :type, :via, :bucket]
    @type t :: %__MODULE__{}
  end

  defmodule Report do
    @moduledoc false
    defstruct axioms: [],
              opaque: [],
              builtin_count: 0,
              holes: [],
              absurd: 0,
              not_proven_total: [],
              unresolved: [],
              unaudited: []

    @type t :: %__MODULE__{}
  end

  # Verified to elaborate on this branch, yielding 42 defs.
  @prelude_probe "mod Probe.Empty\nend\n"

  @doc "The defs every module gets for free."
  @spec prelude_env() :: Env.t()
  def prelude_env do
    {:ok, env} = Program.elaborate(@prelude_probe)
    env
  end

  @doc """
  The defs the audited module owns.

  Canonical definition identity is authoritative: a module-local definition,
  including one emitted by a macro, is keyed as `Module#name`. Imported and
  ambient definitions remain available for the reachability walk, but are not
  roots merely because an interface projection differs from the probe env.
  """
  @spec roots(Env.t()) :: [atom()]
  def roots(%Env{defs: defs, module_owner: owner}) when is_binary(owner) do
    defs
    |> Enum.filter(fn {name, definition} ->
      Cure.Elab.Name.owner(name) == owner and Map.get(definition, :body) != nil
    end)
    |> Enum.map(&elem(&1, 0))
    |> Enum.sort()
  end

  # Compatibility for synthetic/legacy environments with no canonical owner.
  def roots(%Env{defs: defs}) do
    prelude = prelude_env().defs

    # Diff on (name, body), not name alone. A module may redefine a prelude name
    # — e.g. `fn eq(...) = @extern(...)` — and elaboration is deterministic, so a
    # genuine prelude def has a byte-identical body in both envs while a
    # shadowing redefinition does not. Keying on name alone would exclude the
    # shadow from roots and, if nothing else referenced it, hide the axiom
    # entirely: a fail-open hole in a fail-closed tool.
    names =
      for {name, d} <- defs,
          Map.get(prelude, name) == nil or Map.get(prelude, name).body != d.body,
          do: name

    Enum.sort(names)
  end

  @spec bucket({atom(), atom(), non_neg_integer()}) :: :otp | :cure_runtime | :cure_bridge
  def bucket({m, _f, _a}) do
    s = Atom.to_string(m)

    cond do
      String.starts_with?(s, "cure_std_") -> :cure_runtime
      String.starts_with?(s, "Elixir.Cure.") -> :cure_bridge
      true -> :otp
    end
  end

  @spec audit_source(String.t(), String.t()) :: Report.t()
  def audit_source(source, label) do
    case Program.elaborate(source) do
      {:ok, env} -> audit_env(env)
      {:error, reason} -> %Report{unaudited: [{label, reason}]}
    end
  end

  @spec audit_env(Env.t()) :: Report.t()
  def audit_env(%Env{} = env) do
    {reachable, unresolved} = reachable(env, roots(env))

    axioms =
      for name <- reachable,
          def = Map.fetch!(env.defs, name),
          match?({:extern, _}, def.body) do
        {:extern, mfa} = def.body
        %Axiom{mfa: mfa, type: print_type(def.type), via: name, bucket: bucket(mfa)}
      end
      |> Enum.uniq_by(fn a -> {a.mfa, a.type} end)
      |> Enum.sort_by(&sort_key/1)

    scans = for name <- reachable, do: Refs.scan(Map.fetch!(env.defs, name).body)

    %Report{
      axioms: axioms,
      opaque: opaque_types(env, reachable),
      builtin_count:
        env.defs
        |> Enum.flat_map(fn {_name, definition} -> List.wrap(Map.get(definition, :builtin_op)) end)
        |> Enum.uniq()
        |> length(),
      holes: scans |> Enum.flat_map(& &1.holes) |> Enum.sort(),
      absurd: scans |> Enum.map(& &1.absurd) |> Enum.sum(),
      not_proven_total: not_proven_total(env, reachable),
      unresolved: unresolved,
      unaudited: []
    }
  end

  # Sorted, stable, and independent of map iteration order.
  defp sort_key(%Axiom{mfa: {m, f, a}, type: t}), do: {Atom.to_string(m), Atom.to_string(f), a, t}

  # `Effect(T)` is a valid Core type former, but the trusted Core printer is
  # intentionally outside this audit module's ownership boundary. Keep audit
  # reporting total by handling the former here and delegating every other
  # type to the existing printer.
  defp print_type({:effect_type, payload}), do: "Effect(#{print_type(payload)})"

  defp print_type(type) do
    Printer.print(type)
  rescue
    ArgumentError -> inspect(type)
  end

  # Our own walk. NOT Program.reachable_def_names/2, whose collect_reachable/4
  # skips builtin_op defs and type-level defs — correct for codegen, and
  # catastrophic here, because the first drops arithmetic, which is an axiom.
  #
  # Returns `{reachable_def_names, unresolved_global_names}`.
  #
  # The design spec asserted an unresolved global was unreachable on a checked
  # env, citing `Kernel.infer/2`'s `{:error, :unknown_global}`. That is false for
  # a def's *type*: `Std.Fsm` declares `fn spawn(fsm_module: Atom) -> Pid` where
  # `Pid` is neither a def, a family, nor a constructor, and the module
  # elaborates — because a bodyless `@extern` is a postulate whose signature is
  # believed, not checked. Raising here would make the tool unable to audit
  # Std.Fsm, Std.Actor, Std.Supervisor and Std.Process. It is a finding, and a
  # sharp one: an axiom whose type names something that does not exist.
  # An opaque type belongs on the audited module's trust surface when the module
  # declares it, or when a reachable definition mentions it — in a signature or
  # in a body. Listing every opaque family in the environment instead reports the
  # prelude's: `Std.Tuple#Tuple` is ambient, so every module in the language
  # would be told it depends on an opaque `Tuple` it never names. Ownership is
  # decided the same way `roots/1` decides it, by canonical definition identity.
  defp opaque_types(env, reachable) do
    mentioned =
      reachable
      |> Enum.flat_map(fn name ->
        definition = Map.fetch!(env.defs, name)
        Refs.families(Map.get(definition, :type)) ++ Refs.families(Map.get(definition, :body))
      end)
      |> MapSet.new()

    env.families
    |> Map.keys()
    |> Enum.filter(&Cure.Core.Inductive.opaque?(env, &1))
    |> Enum.reject(&(&1 in Map.values(env.builtins)))
    |> Enum.filter(&(declared_here?(env, &1) or MapSet.member?(mentioned, &1)))
    |> Enum.sort()
  end

  defp declared_here?(%Env{module_owner: owner}, family) when is_binary(owner),
    do: Cure.Elab.Name.owner(family) == owner

  # Synthetic/legacy environments carry no canonical owner. Fall back to the same
  # prelude diff `roots/1` uses: anything the empty-module probe does not already
  # have was declared by the source under audit.
  defp declared_here?(%Env{}, family), do: not Map.has_key?(prelude_env().families, family)

  defp reachable(env, roots) do
    {seen, unresolved} =
      Enum.reduce(roots, {MapSet.new(), MapSet.new()}, fn root, acc -> collect(env, root, acc) end)

    {seen |> MapSet.to_list() |> Enum.sort(), unresolved |> MapSet.to_list() |> Enum.sort()}
  end

  defp collect(env, name, {seen, unresolved} = acc) do
    cond do
      MapSet.member?(seen, name) or MapSet.member?(unresolved, name) ->
        acc

      def = Map.get(env.defs, name) ->
        seen = MapSet.put(seen, name)
        refs = Refs.globals(def.type) ++ Refs.globals(def.body)
        Enum.reduce(refs, {seen, unresolved}, fn ref, a -> collect(env, ref, a) end)

      # A global may name a type family or a constructor rather than a def.
      # Those are resolved; they simply do not live in `env.defs`.
      Map.has_key?(env.families, name) or Map.has_key?(env.ctors, name) ->
        acc

      true ->
        {seen, MapSet.put(unresolved, name)}
    end
  end

  # A completeness limit, not an assumption: an uncertified def never δ-unfolds,
  # so the kernel cannot use it to inhabit a type. Externs have no body to
  # certify, and builtin ops are a kernel baseline; both are excluded.
  defp not_proven_total(%Env{totality_certified: nil}, _reachable), do: []

  defp not_proven_total(%Env{} = env, reachable) do
    for name <- reachable,
        def = Map.fetch!(env.defs, name),
        not Env.total?(env, name),
        is_nil(Map.get(def, :builtin_op)),
        not match?({:extern, _}, def.body),
        do: name
  end
end
