defmodule Cure.Elab.Union do
  @moduledoc """
  Canonicalisation and family generation for anonymous union types (`Int | String`).

  A union's IDENTITY is its canonical member list: flattened, normalised to full
  normal form, keyed by a type-distinguishing printing, deduped, and lexically
  sorted. That sorted key list *names* the generated family, so `Int | String` and
  `String | Int` produce literally the same `{:data, name}` and are definitionally
  equal with **zero kernel involvement** — no new type former, no conversion rule,
  no subtyping, no cast.

  ## Key format

  A **type** member keys as its printed Core type: `Int`, `List(Int)`.

  A **literal** member keys as `<TypeKey>#<printed value>`: `Int#3`, `String#"4"`,
  `Atom#:4`, `Char#'c'`, `Bool#true`, `Float#4.0`. The `<TypeKey>#` prefix is what
  keeps `"4"` (a `String`) and `:4` (an `Atom`) from colliding on `4`.

  ## Constructor names are family-qualified

  `env.ctors` is a **global flat map** (`Cure.Core.Inductive.declare/3`), so a bare
  `:Int` constructor would collide across two different unions that each have an
  `Int` member, and `ctor_to_family` would point at the wrong family. Constructor
  names are therefore `:"<union_key>$<member_key>"`.

  See `docs/superpowers/specs/2026-07-11-anonymous-adts-design.md`.
  """

  alias Cure.Core.{Context, Env, Inductive, Normalise}

  @type member :: %{
          key: String.t(),
          payload: nil | tuple(),
          lit_type_key: nil | String.t()
        }

  @union_prefix "Union<"
  @disjoint_prefix "Disjoint<"
  @prefixes [@union_prefix, @disjoint_prefix]

  # Structural separators of the generated key grammar: `Union<a|b>$Int#3`.
  @key_separators ["<", ">", "|", "$", "#"]

  # ── Public API ─────────────────────────────────────────────────────────────

  @doc "True iff `atom` is a generated family key — `Union<…>` or `Disjoint<…>`."
  @spec union_family?(atom()) :: boolean()
  def union_family?(atom) when is_atom(atom) do
    s = Atom.to_string(atom)
    Enum.any?(@prefixes, &String.starts_with?(s, &1))
  end

  def union_family?(_), do: false

  @doc "The reserved prefixes a user-declared type name may not take."
  @spec reserved_prefixes() :: [String.t()]
  def reserved_prefixes, do: @prefixes

  @doc """
  Is `name` reserved — i.e. would a user declaration of it be able to collide with, absorb,
  or overwrite a compiler-generated family or constructor?

  Two ways it can:

    * it carries a generated PREFIX (`Union<…>`, `Disjoint<…>`), so it can be the family
      atom itself; or
    * it contains a SEPARATOR of the key grammar. Family keys join member keys with `|`
      inside `<…>`; constructors are `<family>$<member_key>`; a literal member keys as
      `<TypeKey>#<value>`. So `< > | $ #` are all structural. A type named `` `Int#3` ``
      keys as `"Int#3"` — byte-identical to the literal `3` — and the two silently dedupe
      against each other, dropping a member from the union with no diagnostic.

  None of these characters is producible by an ordinary identifier; all are reachable in a
  BACKTICK-quoted one, which is the whole attack surface.
  """
  @spec reserved_name?(atom() | String.t()) :: boolean()
  def reserved_name?(name) when is_atom(name), do: reserved_name?(Atom.to_string(name))

  def reserved_name?(name) when is_binary(name) do
    Enum.any?(@prefixes, &String.starts_with?(name, &1)) or
      String.contains?(name, @key_separators)
  end

  @doc """
  The generated family key for a canonical member list.

  The PREFIX is not cosmetic — it says whether the constructor tag is LOAD-BEARING:

    * `Union<k1|k2|…>` — the members' erased value sets are pairwise DISJOINT, so the
      tagged sum and a set union coincide. Nothing can be both an `Int` and a `String`,
      so the tag is an implementation detail you could not observe.

    * `Disjoint<k1|k2|…>` — two members' value sets OVERLAP (`{3} ⊆ Int`, `true`/`false`
      ⊆ atoms), so this is ONLY a disjoint sum. The tag is precisely what keeps `Int(3)`
      and `Lit3` apart, and which one a value carries depends on how it was WRITTEN, not
      on what it equals. Calling that a "union" would be a lie.

  `<`, `>` and `|` are not producible by the type-name lexer, so neither key can collide
  with a user-declared type.
  """
  @spec family_key([member()], Env.t()) :: atom()
  def family_key(members, env) do
    prefix = if disjoint_only?(members, env), do: @disjoint_prefix, else: @union_prefix
    inner = members |> Enum.map(& &1.key) |> Enum.join("|")

    String.to_atom(prefix <> inner <> ">")
  end

  @doc """
  Do any two members' ERASED value sets overlap — i.e. is this a disjoint sum that a set
  union cannot model?

  Two LITERALS never overlap (distinct values; canonicalisation dedupes). Otherwise the
  members overlap when their runtime classes coincide, when one refines the other
  (`Bool` ⊂ `Atom`), or when a literal falls inside a type member's class (`3` ∈ `Int`).
  """
  @spec disjoint_only?([member()], Env.t()) :: boolean()
  def disjoint_only?(members, env) do
    Enum.any?(members, fn a ->
      Enum.any?(members, fn b -> a.key < b.key and members_overlap?(a, b, env) end)
    end)
  end

  # Two LITERALS overlap iff they ERASE to the same Erlang value. Distinct KEYS are not
  # enough: different literal TYPES can share an erasure — Char `'A'` and Int `65` are both
  # the integer 65; Bool `true` and Atom `:true` are both the atom `true`. Assuming
  # "two literals never overlap" made `discriminable/1` certify a union it cannot
  # discriminate, and named it `Union<…>` when the tag was in fact load-bearing.
  defp members_overlap?(%{payload: nil} = a, %{payload: nil} = b, _env),
    do: literal_value(a.key) == literal_value(b.key)

  defp members_overlap?(a, b, env),
    do: class_overlap?(runtime_class(env, a), runtime_class(env, b))

  # A user ADT (`:unsupported`) erases to a bare atom when nullary, so it overlaps `Atom`.
  # Two DIFFERENT ADTs never overlap — constructor names are globally unique — and an ADT
  # collides with neither integer/float/binary/list nor `Bool`, whose only inhabitants are
  # the atoms `true`/`false`, which no ADT constructor can be named.
  defp class_overlap?(:unsupported, :unsupported), do: false
  defp class_overlap?(:unsupported, :atom), do: true
  defp class_overlap?(:atom, :unsupported), do: true
  defp class_overlap?(c, c), do: true
  defp class_overlap?(a, b), do: refines?(a, b) or refines?(b, a)

  @doc "The constructor name for `member` within family `family_key`."
  @spec ctor_key(atom(), member() | %{key: String.t()}) :: atom()
  def ctor_key(family_key, %{key: k}) do
    String.to_atom(Atom.to_string(family_key) <> "$" <> k)
  end

  @doc """
  The canonical key of a literal, from its surface subtype and value.

  Single source of truth: both `lower_member/3` here and the elaborator's
  check-position literal injection call this, so the two can never drift into
  producing a constructor name that does not exist.
  """
  @spec literal_key(atom(), term()) :: {:ok, String.t()} | :error
  def literal_key(:integer, v) when is_integer(v), do: {:ok, "Int#" <> Integer.to_string(v)}
  def literal_key(:float, v) when is_float(v), do: {:ok, "Float#" <> Float.to_string(v)}
  def literal_key(:string, v) when is_binary(v), do: {:ok, "String#" <> ~s("#{v}")}
  def literal_key(:symbol, v) when is_atom(v), do: {:ok, "Atom#:" <> Atom.to_string(v)}
  def literal_key(:char, v) when is_integer(v), do: {:ok, "Char#'" <> <<v::utf8>> <> "'"}
  def literal_key(:boolean, v) when is_boolean(v), do: {:ok, "Bool#" <> to_string(v)}
  def literal_key(_subtype, _value), do: :error

  @doc """
  Canonicalise a list of surface member ASTs into a sorted, deduped member list.

  Returns `{:error, {:union_member_not_ground, ast}}` for a member with a free type
  variable or an unsolved metavariable.

  A literal unioned with its OWN type (`Int | 3`) is ADMITTED — see the note at the
  bottom of this module. It is disambiguated by most-specific-wins, not rejected.
  """
  @spec canonicalise([tuple()], [String.t()], Env.t()) :: {:ok, [member()]} | {:error, term()}
  def canonicalise(asts, scope, env) do
    with {:ok, raw} <- lower_members(asts, scope, env) do
      members =
        raw
        |> Enum.concat()
        |> Enum.uniq_by(& &1.key)
        |> Enum.sort_by(& &1.key)

      {:ok, members}
    end
  end

  @doc "The type-distinguishing canonical printing of a lowered, nf'd Core type."
  @spec member_key(tuple()) :: String.t()
  # NOTE(int-facade): `member_key`/`class_of_core` below are kept for totality
  # on a legacy/deserialized `{:int_type}` node; fresh elaboration never
  # produces one (spec 2026-07-18 §3a).
  def member_key({:int_type}), do: "Int"
  def member_key({:float_type}), do: "Float"
  def member_key({:binary_type}), do: "Binary"
  def member_key({:atom_type}), do: "Atom"
  def member_key({:type, l}), do: "Type" <> Integer.to_string(l)

  def member_key({:data, name, params, indices}) do
    case params ++ indices do
      [] -> Atom.to_string(name)
      args -> Atom.to_string(name) <> "(" <> Enum.map_join(args, ",", &member_key/1) <> ")"
    end
  end

  def member_key({:nat_lit, n}), do: Integer.to_string(n)
  def member_key({:int_lit, n}), do: Integer.to_string(n)
  def member_key({:float_lit, f}), do: Float.to_string(f)
  def member_key({:bounded_lit, k}), do: Integer.to_string(k)
  def member_key({:atom_lit, a}), do: ":" <> Atom.to_string(a)
  def member_key({:ctor, name, []}), do: Atom.to_string(name)
  def member_key({:global, name}), do: Atom.to_string(name)

  # ── FFI boundary: runtime discrimination ───────────────────────────────────

  @doc """
  The ERASED runtime shape of a member, as the Erlang guard that recognises it.

  This is what makes a union-returning `@extern` possible: Erlang hands back an untagged
  value, and the boundary can only re-tag it if each member is recognisable.

  Note `Bool` is `:boolean`, NOT `:atom`. It erases to the atoms `true`/`false`, but
  `is_boolean/1` is a real, total Erlang guard that strictly REFINES `is_atom/1` — so
  `Bool | Atom` is perfectly discriminable *by order* (see `refines?/2`). The question is
  never "do two members share a class", it is "can one member's guard be ordered before
  the other's".

  `:unsupported` for anything whose erasure is not a single recognisable shape — a user
  ADT erases to a bare atom when nullary and a tagged tuple otherwise, so it is BOTH
  shapes at once and no single guard recognises it.

  Takes `env` because a family's class is not always a function of its NAME. An
  `opaque type` has no constructors, so its erasure cannot be inferred from anything —
  it is DECLARED, with `@erases(<class>)`, and that declaration lives on the family in
  `env`. A member cannot cache its own class, either: `members_of/2` rebuilds members
  from the family key, so the class must be re-derivable from the key plus `env`.
  """
  @spec runtime_class(Env.t(), member()) :: atom()
  def runtime_class(_env, %{payload: nil, lit_type_key: t}), do: class_of_type_key(t)
  def runtime_class(env, %{payload: ty}), do: class_of_core(env, ty)

  defp class_of_core(_env, {:int_type}), do: :integer
  defp class_of_core(_env, {:float_type}), do: :float
  defp class_of_core(_env, {:binary_type}), do: :binary
  defp class_of_core(_env, {:atom_type}), do: :atom

  defp class_of_core(env, {:data, name, _p, _i}) do
    declared_erasure(env, name) || class_of_data_name(bare_family_name(name))
  end

  defp class_of_core(_env, _other), do: :unsupported

  # The `@erases(<class>)` a sealed FFI module declared for an opaque carrier. Only an
  # opaque family can carry one (`Declarations.reject_erases_on_non_opaque/1`), so this
  # never overrides a class the erasure of a real constructor set already determines.
  #
  # Looked up under the name AS WRITTEN first, then under the bare name: after
  # `Resolution.rekey_module_env/3` the family is registered under its qualified
  # `:"<module_id>#<name>"` key and the member payload names it that way too, but the
  # rekey PASS itself recomputes `family_key/2` against the pre-rekey `env`, where only
  # the bare name is registered.
  defp declared_erasure(env, name) do
    family =
      Inductive.get_family(env, name) || Inductive.get_family(env, bare_family_name(name))

    case family do
      nil -> nil
      f -> Map.get(f, :erasure)
    end
  end

  defp class_of_data_name(:Bool), do: :boolean
  # `Int` is now the inductive family Std.Int#Int (spec 2026-07-18 surface flip); it
  # erases to a native BEAM integer, exactly like `Nat`, so its runtime guard class is
  # `:integer` (this is what the retired `class_of_core({:int_type})` clause provided).
  defp class_of_data_name(:Int), do: :integer
  defp class_of_data_name(:Nat), do: :integer
  defp class_of_data_name(:Bounded), do: :integer
  defp class_of_data_name(:List), do: :list
  defp class_of_data_name(_other), do: :unsupported

  # `Resolution.rekey_module_env/3` re-keys a SHADOWED family to a qualified
  # `:"<module_id>#<name>"` atom (`rekey_atom/2`) and then recomputes this union's
  # `family_key/1` from the rewritten member set — so `class_of_core/1` must
  # recognise a rekeyed `Bool`/`Nat`/`Bounded`/`List` as itself, or the recomputed
  # `disjoint_only?/1` sees `:unsupported` instead of the family's real erasure
  # class. That silently FLIPS the `Union<…>`/`Disjoint<…>` prefix on rekey: `Nat`
  # and `Int` both erase to Erlang integers and genuinely overlap (`Disjoint<…>`,
  # tag load-bearing), but `class_overlap?(:unsupported, :integer)` is `false`, so
  # a rekeyed `Nat | Int` would silently reclassify as `Union<…>` — claiming the
  # erased value sets are disjoint when they are not. Rekeying changes a family's
  # NAME, never its own runtime erasure, so the classification must see through
  # the qualifier. `module_id` (built by `rekey_atom/2` from a dotted module path)
  # never itself contains `#`, so splitting on the FIRST `#` is exact.
  defp bare_family_name(name) do
    case name |> Atom.to_string() |> String.split("#", parts: 2) do
      [_module_id, bare] -> String.to_atom(bare)
      [bare] -> String.to_atom(bare)
    end
  end

  defp class_of_type_key("Int"), do: :integer
  defp class_of_type_key("Nat"), do: :integer
  defp class_of_type_key("Char"), do: :integer
  defp class_of_type_key("Float"), do: :float
  defp class_of_type_key("Binary"), do: :binary
  defp class_of_type_key("Atom"), do: :atom
  defp class_of_type_key("Bool"), do: :boolean
  defp class_of_type_key("String"), do: :list
  defp class_of_type_key(_other), do: :unsupported

  @doc """
  Does guard class `a` strictly REFINE class `b` — i.e. is every value `a` accepts also
  accepted by `b`, so that ordering `a` first discriminates them?

  `is_boolean/1` ⊂ `is_atom/1` is the only such pair among Cure's erased shapes.

  Deliberately NOT extended to `Nat`/`Char` ⊂ `Int`: those would need a range predicate,
  and the resulting precedence ("a small non-negative integer is ALWAYS a Nat, never an
  Int") is surprising in a way "`true` is always a Bool" is not. They stay rejected.
  """
  @spec refines?(atom(), atom()) :: boolean()
  def refines?(:boolean, :atom), do: true
  def refines?(_a, _b), do: false

  @doc """
  Can every member of this union be told apart from an untagged Erlang value?

  Returns `:ok`, or `{:error, reason}` naming the members that cannot be separated.

  Discrimination is ORDERED, most-specific-first:

    1. **Literal** members test the exact value (`R =:= north`). An exact test refines
       every class guard, so a literal may freely share a class with a type member — the
       sentinel pattern `3 | Nat` ("a raw 3 is the sentinel, any other integer is a Nat")
       is admissible and total.
    2. **Type** members test their class guard, ordered so that a refining guard comes
       first — `Bool` (`is_boolean`) before `Atom` (`is_atom`).

  Two TYPE members conflict only when they share a class and neither refines the other:
  `Int | Nat` (both integers), `String | List(Int)` (both lists). No order separates
  those, so they are rejected.
  """
  @spec discriminable([member()], Env.t()) :: :ok | {:error, term()}
  def discriminable(members, env) do
    {lits, types} = Enum.split_with(members, &(&1.payload == nil))

    classes = Enum.map(types ++ lits, &{&1.key, runtime_class(env, &1)})
    unsupported = for {k, :unsupported} <- classes, do: k

    # Only TYPE members can collide: a literal is an exact-value test, which refines any
    # class guard and is emitted first.
    collisions =
      for {ka, ca} <- Enum.map(types, &{&1.key, runtime_class(env, &1)}),
          {kb, cb} <- Enum.map(types, &{&1.key, runtime_class(env, &1)}),
          ka < kb,
          ca == cb or (not refines?(ca, cb) and not refines?(cb, ca) and ca == cb),
          do: {ka, kb, ca}

    # Two literals that ERASE to the same value cannot be told apart by any guard — their
    # exact-value tests are byte-identical, so the second clause is dead and the second
    # constructor is unreachable. `'A' | 65`, `true | :true`.
    lit_collisions =
      for a <- lits,
          b <- lits,
          a.key < b.key,
          literal_value(a.key) == literal_value(b.key),
          do: {a.key, b.key}

    cond do
      unsupported != [] -> {:error, {:unsupported_member_shape, unsupported}}
      collisions != [] -> {:error, {:same_runtime_shape, collisions}}
      lit_collisions != [] -> {:error, {:same_erased_literal, lit_collisions}}
      true -> :ok
    end
  end

  @doc """
  Rebuild the SURFACE literal node behind a literal member's key.

  Needed by the elaborator: a literal member binds no payload, so an arm that NAMES it
  (`n: 3`) must substitute that name with the literal itself.
  """
  @spec literal_surface(String.t()) :: {:ok, tuple()} | :error
  def literal_surface(key) do
    case String.split(key, "#", parts: 2) do
      ["Int", v] -> {:ok, {:literal, [subtype: :integer], String.to_integer(v)}}
      ["Nat", v] -> {:ok, {:literal, [subtype: :integer], String.to_integer(v)}}
      ["Float", v] -> {:ok, {:literal, [subtype: :float], String.to_float(v)}}
      ["Bool", v] -> {:ok, {:literal, [subtype: :boolean], v == "true"}}
      ["Atom", ":" <> v] -> {:ok, {:literal, [subtype: :symbol], String.to_atom(v)}}
      ["Char", <<?', c::utf8, ?'>>] -> {:ok, {:literal, [subtype: :char], c}}
      ["String", <<?", rest::binary>>] -> {:ok, {:literal, [subtype: :string], strip_one_trailing_quote(rest)}}
      _ -> :error
    end
  end

  @doc """
  The VALUE RANGE a type member's erased representation must satisfy, beyond its guard —
  `nil` when the guard alone is exact.

  A guard must never be WIDER than the member's value set, or the FFI wrapper manufactures
  a value the author never asserted. `Nat` erases to a plain integer, but `is_integer` also
  accepts negatives, so a raw `-7` was being tagged `Nat(-7)`. `Bounded(n)` (hence `Char`)
  is likewise an integer confined to `0..n-1`.
  """
  @spec value_bounds(member()) :: nil | {non_neg_integer(), non_neg_integer() | :infinity}
  def value_bounds(%{payload: {:data, name, _params, indices}}) do
    case bare_family_name(name) do
      :Nat ->
        {0, :infinity}

      :Bounded ->
        case indices do
          [{:nat_lit, n}] -> {0, n}
          # An unknown bound still cannot be negative.
          _ -> {0, :infinity}
        end

      _ ->
        nil
    end
  end

  def value_bounds(_member), do: nil

  @doc """
  Members ordered for runtime discrimination: literals (exact value) first, then type
  members with refining guards ahead of the guards they refine.
  """
  @spec discrimination_order([member()], Env.t()) :: [member()]
  def discrimination_order(members, env) do
    {lits, types} = Enum.split_with(members, &(&1.payload == nil))

    # Sort by an explicit SPECIFICITY RANK, not by `refines?/2` directly.
    #
    # `refines?/2` is not a valid `Enum.sort/2` comparator: it is a STRICT relation, so it
    # returns false for unrelated pairs, which sort reads as "a > b". The ordering of
    # unrelated members is then undefined, and the one invariant that MUST hold — a
    # refining guard precedes the guard it refines — would be guaranteed only by luck of
    # the merge-sort internals rather than by contract. A rank is a total order, so it is.
    lits ++ Enum.sort_by(types, &specificity(runtime_class(env, &1)))
  end

  # Lower rank = tested earlier. `is_boolean` must precede `is_atom`; every other guard is
  # mutually exclusive of the rest, so its relative rank is immaterial.
  defp specificity(:boolean), do: 0
  defp specificity(_other), do: 1

  @doc """
  The literal value behind a LITERAL member's key, for building an equality guard.

  The key format is `<TypeKey>#<printed>` and we generated it, so this is a total inverse
  for the six literal type-keys. Only ever called on a NULLARY ctor's key, so a rekeyed
  module-qualified TYPE name (`Std.Foo#Foo`, which also contains `#`) can never reach it.
  """
  @spec literal_value(String.t()) :: {:ok, atom(), term()} | :error
  def literal_value(key) do
    case String.split(key, "#", parts: 2) do
      ["Int", v] -> {:ok, :integer, String.to_integer(v)}
      ["Nat", v] -> {:ok, :integer, String.to_integer(v)}
      ["Float", v] -> {:ok, :float, String.to_float(v)}
      ["Bool", v] -> {:ok, :atom, v == "true"}
      ["Atom", ":" <> v] -> {:ok, :atom, String.to_atom(v)}
      ["Char", <<?', c::utf8, ?'>>] -> {:ok, :integer, c}
      ["String", <<?", rest::binary>>] -> {:ok, :string, strip_one_trailing_quote(rest)}
      _ -> :error
    end
  end

  # `literal_key(:string, v)` builds the key as `"String#\"" <> v <> "\""` with NO
  # escaping of `v` — so `rest` here is always exactly `v <> "\""`, regardless of what
  # characters `v` itself contains (including a trailing `"`). The correct inverse is
  # "drop exactly the one closing quote byte we know is there by construction", NOT
  # `String.trim_trailing(rest, "\"")`, which strips EVERY trailing `"` and so silently
  # truncates a value that itself ends in one or more quote characters (e.g. `v = ~s(ab")`
  # round-tripped to `"ab"`, dropping the trailing quote that is part of the value).
  # The closing quote is a single ASCII byte, so a byte-precise drop is always exact,
  # including when `v` contains multi-byte UTF-8 content earlier in the string.
  defp strip_one_trailing_quote(rest), do: binary_part(rest, 0, byte_size(rest) - 1)

  # ── Family generation ──────────────────────────────────────────────────────

  @doc """
  Declare the generated family for a union's surface members, idempotently.

  Returns `{:ok, env, {:data, key, [], []}}` for a real union, or `{:ok, env, core}`
  for a one-member union of a TYPE member, which collapses to that member itself —
  no family is generated. A one-member union of a LITERAL member still needs a
  family: there is no Core term for a bare literal in type position.
  """
  @spec declare([tuple()], [String.t()], Env.t()) :: {:ok, Env.t(), tuple()} | {:error, term()}
  def declare(asts, scope, env) do
    with {:ok, members} <- canonicalise(asts, scope, env) do
      case members do
        [%{payload: payload}] when payload != nil -> {:ok, env, payload}
        _ -> declare_family(members, env)
      end
    end
  end

  defp declare_family(members, env) do
    key = family_key(members, env)

    if Inductive.family?(env, key) do
      # Idempotent: the key is content-derived, so re-declaring an identical family
      # would be an identical Map.put.
      {:ok, env, {:data, key, [], []}}
    else
      ctors =
        Enum.map(members, fn m ->
          cname = ctor_key(key, m)

          case m.payload do
            nil -> Inductive.ctor(cname, [], [], [], [])
            ty -> Inductive.ctor(cname, [{:v, ty}], [], [Cure.Core.Grade.unrestricted()], [])
          end
        end)

      case Cure.Elab.Declarations.declare_generated_family(env, key, ctors) do
        {:ok, env2} -> {:ok, env2, {:data, key, [], []}}
        {:error, _} = err -> err
      end
    end
  end

  @doc """
  Walk a declaration's AST, declaring the family for every `{:union_type, …}` in it.

  This exists as a PRE-PASS because `idx_to_core/5` returns `{:ok, term}` and cannot
  thread a mutated `Env` back out to its callers — so a union family cannot be
  declared as a side-effect of type lowering. `Declarations.elaborate/2` *does*
  return `{:ok, Env.t()}`, so the declaration happens there and lowering merely looks
  the key up.
  """
  @spec predeclare_all(term(), Env.t()) :: {:ok, Env.t()} | {:error, term()}
  def predeclare_all(ast, env) do
    ast
    |> collect_unions()
    |> Enum.reduce_while({:ok, env}, fn {:union_type, _meta, members}, {:ok, env} ->
      case declare(members, [], env) do
        {:ok, env2, _core} -> {:cont, {:ok, env2}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # Innermost-first, so a nested union has its inner family declared before the outer
  # one tries to splice it in.
  defp collect_unions(node) when is_tuple(node) do
    inner = node |> Tuple.to_list() |> Enum.flat_map(&collect_unions/1)
    if match?({:union_type, _, _}, node), do: inner ++ [node], else: inner
  end

  defp collect_unions(list) when is_list(list), do: Enum.flat_map(list, &collect_unions/1)
  defp collect_unions(_other), do: []

  # ── Lowering ───────────────────────────────────────────────────────────────

  defp lower_members(asts, scope, env) do
    Enum.reduce_while(asts, {:ok, []}, fn ast, {:ok, acc} ->
      case lower_member(ast, scope, env) do
        {:ok, ms} -> {:cont, {:ok, acc ++ [ms]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  # A LITERAL member becomes a NULLARY constructor: the value is fully determined by
  # the constructor, so there is nothing to store.
  defp lower_member({:literal, meta, value} = ast, _scope, _env) do
    case literal_key(Keyword.get(meta, :subtype), value) do
      {:ok, key} ->
        [type_key, _printed] = String.split(key, "#", parts: 2)
        {:ok, [%{key: key, payload: nil, lit_type_key: type_key}]}

      :error ->
        {:error, {:union_member_not_ground, ast}}
    end
  end

  # A TYPE member is lowered to Core and reduced to FULL normal form.
  #
  # `nf`, not `whnf`: plain evaluation leaves a neutral global application inside an
  # index (`Bounded(1+1)`) stuck rather than folding it to `Bounded(2)`. Without full
  # normal form, two definitionally-equal ground members would print as different
  # keys and silently produce two distinct families for one type.
  defp lower_member(ast, scope, env) do
    with {:ok, core} <- Cure.Elab.Declarations.lower_type(ast, scope, env) do
      case Normalise.nf(Context.empty(env), core, delta: :certified) do
        :fuel_exhausted ->
          {:error, {:union_member_not_ground, ast}}

        nf ->
          cond do
            # A member that is ITSELF a union splices its members in — this is how
            # `(A | B) | C` flattens and how a `typealias P = Int | String` used as a
            # member unfolds.
            match?({:data, _, [], []}, nf) and union_family?(elem(nf, 1)) ->
              {:ok, explode(env, elem(nf, 1))}

            ground?(nf, env) ->
              {:ok, [%{key: member_key(nf), payload: nf, lit_type_key: nil}]}

            true ->
              {:error, {:union_member_not_ground, ast}}
          end
      end
    end
  end

  @doc """
  Recover a union family's canonical members from its registered constructors: a nullary
  ctor is a literal member, a 1-ary ctor is a type member whose payload is its single
  argument's type.
  """
  @spec members_of(Env.t(), atom()) :: [member()]
  def members_of(env, family_key), do: explode(env, family_key)

  defp explode(env, family_key) do
    prefix = Atom.to_string(family_key) <> "$"

    env
    |> Inductive.ctors_of(family_key)
    |> Enum.map(fn ctor ->
      key = ctor.name |> Atom.to_string() |> String.replace_prefix(prefix, "")

      case ctor.args do
        [] -> %{key: key, payload: nil, lit_type_key: lit_type_key_of(key)}
        [{_name, ty}] -> %{key: key, payload: ty, lit_type_key: nil}
      end
    end)
  end

  # "Int#3" -> "Int". Only ever called on a key that came from a NULLARY ctor, i.e. a
  # literal member, which always has the `<TypeKey>#<value>` shape.
  defp lit_type_key_of(key) do
    case String.split(key, "#", parts: 2) do
      [t, _v] -> t
      _ -> nil
    end
  end

  # A member is ground iff its Core term has no free variables and no metavariables.
  # Members are lowered in an empty scope, so any `{:var, _}` is by definition free.
  #
  # A bare lowercase name that resolves to nothing lowers to `{:global, name}` rather
  # than `{:var, _}`, so an unbound `{:global, _}` is also rejected — that is the
  # `a | Int` case.
  defp ground?(term, env) do
    not has?(term, fn
      {:var, _} -> true
      {:meta, _} -> true
      {:global, n} -> not known_global?(env, n)
      _ -> false
    end)
  end

  defp known_global?(env, name) do
    Inductive.family?(env, name) or Env.get_def(env, name) != nil
  end

  defp has?(term, pred) when is_tuple(term) do
    if pred.(term) do
      true
    else
      term |> Tuple.to_list() |> Enum.any?(&has?(&1, pred))
    end
  end

  defp has?(list, pred) when is_list(list), do: Enum.any?(list, &has?(&1, pred))
  defp has?(_other, _pred), do: false

  # ── A literal unioned with its OWN type ────────────────────────────────────
  #
  # `Int | 3` and `:north | Atom` are ADMITTED. They were once rejected as an ambiguous
  # injection ("does `3` become the literal member or the `Int` member?"), but that
  # ambiguity does not exist. The two are disambiguated by MOST-SPECIFIC-WINS — the same
  # precedence the FFI boundary uses:
  #
  #   * a LITERAL expression injects into the literal member. `union_literal_ctor/5` is
  #     the FIRST clause of the elaborator's literal `cond`, so it wins outright.
  #   * anything else injects via its inferred TYPE. `maybe_inject_union/5` keys off the
  #     term's type, which is `Int` — never the singleton.
  #
  # They never compete, so there is nothing to reject.
  #
  # The consequence to internalise: the union is a genuine DISJOINT SUM, not a set union.
  # `Int(3)` and `Lit3` are distinct values of `Int | 3`, and which one you get is decided
  # by how the value was WRITTEN, not by what it equals. That is exactly what makes the
  # sentinel pattern work (`-1 | Int`, `:north | Atom`), and at the FFI boundary the same
  # precedence re-tags a raw `3` as the sentinel and any other integer as an `Int`.
end
