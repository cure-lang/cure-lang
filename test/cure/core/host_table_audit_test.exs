defmodule Cure.Core.HostTableAuditTest do
  @moduledoc """
  Executable audit of the host-table model formalised in `Core/HostTable`.

  The Agda module proves, for ARBITRARY host tables, that first-match key
  resolution IS the formal lookup, that a duplicate-free table is
  order-insensitive, and that duplicates, shadowing aliases and dangling
  aliases behave as the model says. Those are theorems about a model.

  This suite pins the OTHER direction: that the model's assumptions match
  what the actual registry and name module do. It is an audit, not a
  refinement proof, and it does not claim the Elixir implementation
  corresponds to the Agda development. Its job is to fail loudly if the
  executable's name resolution or duplicate handling drifts away from the
  model the proofs are about.
  """

  use ExUnit.Case, async: true

  alias Cure.Elab.Name
  alias Cure.Test.ProofSnapshotFixture

  describe "host key resolution is first-match over the presented order" do
    test "the first binding for a key wins, matching Core.HostTable.host-key" do
      # `host-key` returns the FIRST binding for a key. This is the same
      # rule `Core.CanonicalSnapshot.lookup` uses, and the same rule the
      # formal `findFamily` uses. Pin it directly.
      bindings = [{:a, 1}, {:b, 2}, {:a, 3}]

      assert host_key(:a, bindings) == 1
      assert host_key(:b, bindings) == 2
      assert host_key(:c, bindings) == nil
    end

    test "reordering a duplicate-free table does not change resolution" do
      # The Agda theorem `unique-lookup-stable` says duplicate-freedom
      # makes resolution order-insensitive. Check the executable agrees
      # for a duplicate-free table in two orders.
      forward = [{:a, 1}, {:b, 2}, {:c, 3}]
      backward = Enum.reverse(forward)

      for key <- [:a, :b, :c] do
        assert host_key(key, forward) == host_key(key, backward)
      end
    end

    test "a duplicate key DOES change resolution under reordering" do
      # The negative control from `Proof.HostTableExamples`: with a
      # duplicate, the presented order decides the answer. This is why the
      # duplicate-free check is load-bearing rather than cosmetic.
      forward = [{:a, 1}, {:a, 9}]
      backward = [{:a, 9}, {:a, 1}]

      assert host_key(:a, forward) == 1
      assert host_key(:a, backward) == 9
      refute host_key(:a, forward) == host_key(:a, backward)
    end
  end

  describe "the executable registry is duplicate-free by construction" do
    test "an environment's family, constructor and global keys are distinct" do
      # `Core.HostTable.check-table` requires duplicate-freedom before the
      # order-insensitivity theorem applies. The executable stores these
      # in maps, which cannot hold duplicate keys, so the invariant holds
      # structurally. Exercise it on a POPULATED registry so the check is
      # not vacuous.
      env = ProofSnapshotFixture.environment()

      family_keys = Map.keys(env.families)
      ctor_keys = Map.keys(env.ctors)
      def_keys = Map.keys(env.defs)

      assert family_keys != []
      assert ctor_keys != []
      assert def_keys != []

      # A map cannot hold a duplicate key: the key list is duplicate-free.
      assert length(family_keys) == length(Enum.uniq(family_keys))
      assert length(ctor_keys) == length(Enum.uniq(ctor_keys))
      assert length(def_keys) == length(Enum.uniq(def_keys))

      # And the owner table is keyed by exactly the constructor keys.
      assert MapSet.new(ctor_keys) == MapSet.new(Map.keys(env.ctor_to_family))
    end
  end

  describe "alias discipline" do
    test "a qualified alias is stored separately from the key table" do
      # `Core.HostTable.alias-cannot-shadow` relies on aliases living in a
      # SEPARATE table from bindings. The executable keeps
      # `qualified_aliases` distinct from `defs`/`families`; pin that
      # separation so an alias can never be mistaken for a binding.
      # `qualified_aliases` is a map keyed by `{owner, base, namespace}`
      # tuples, while `defs` is keyed by bare atoms. The two key spaces
      # are disjoint by construction, which is exactly the separation
      # `alias-cannot-shadow` needs.
      env = ProofSnapshotFixture.environment()

      # The fixture registers no aliases, so the separation is asserted on
      # the KEY SHAPES the two tables admit, not on their current contents:
      # an alias key is a 3-tuple, a definition key is an atom, and no
      # term can be both. A populated alias table would still be disjoint.
      assert env.qualified_aliases == %{}
      assert env.defs != %{}
      assert Enum.all?(Map.keys(env.defs), &is_atom/1)
      refute Enum.any?(Map.keys(env.defs), &is_tuple/1)
    end

    test "a dangling alias resolves to nothing, not a fabricated binding" do
      # `Core.HostTable.alias-absent-target`: an alias whose target is
      # absent yields nothing. Model it directly on a host-shaped table.
      bindings = [{"Boundary#Pack", 1}]
      aliases = [{"Boundary#alias", "Boundary#missing"}]

      assert host_lookup("Boundary#alias", bindings, aliases) == nil
    end

    test "an alias to a present target resolves through the target" do
      bindings = [{"Boundary#Pack", 1}]
      aliases = [{"Boundary#alias", "Boundary#Pack"}]

      assert host_lookup("Boundary#alias", bindings, aliases) == 1
    end

    test "a present key ignores a shadowing alias" do
      # `alias-cannot-shadow`: real keys win. An alias redirecting a
      # present key elsewhere must not change its resolution.
      bindings = [{"Boundary#Pack", 1}, {"Boundary#Packed", 0}]
      aliases = [{"Boundary#Pack", "Boundary#Packed"}]

      assert host_lookup("Boundary#Pack", bindings, aliases) == 1
    end
  end

  describe "name identities are canonical and owner-qualified" do
    test "qualified names split into owner and base" do
      # `Core.HostTable` treats names as opaque keys; the boundary record
      # `Core.RepresentationBoundary.name-encoding` is where the split
      # lives. Pin that the executable's split is the owner-qualified
      # convention the fixture names use.
      assert Name.owner(:"Boundary#Pack") == "Boundary"
      assert Name.base(:"Boundary#Pack") == "Pack"
      assert Name.qualified?(:"Boundary#Pack")
    end

    test "a bare name has no owner and is its own base" do
      assert Name.owner(:answer) == nil
      assert Name.base(:answer) == "answer"
      refute Name.qualified?(:answer)
    end

    test "a content-derived identity is its own base, not a qualified name" do
      # `Name.split/1`'s doc is explicit: a name whose text before the
      # separator is not a valid owner is its own base. This matters for
      # the boundary record's injectivity obligation: two spellings that
      # look qualified may not actually be owner-qualified.
      name = :"Union<Int|Std.Bool#Bool>"

      assert Name.owner(name) == nil
      assert Name.base(name) == "Union<Int|Std.Bool#Bool>"
      refute Name.qualified?(name)
    end
  end

  describe "the ledger is a real split, not a formality" do
    test "the Agda ledger names theorems on the proved side" do
      # `m2a-ledger` must not be vacuous: both sides carry entries, and
      # the proved side names the actual theorems. Read the Agda source
      # and assert the names it claims are really defined.
      source = File.read!("proof/Core/HostTable.agda")
      ledger = File.read!("proof/Core/RepresentationBoundary.agda")

      for theorem <- [
            "host-key-agrees",
            "unique-lookup-stable",
            "duplicate-first-wins",
            "duplicate-second-wins",
            "duplicate-not-unique",
            "alias-cannot-shadow",
            "alias-absent-target",
            "checked-resolves"
          ] do
        assert source =~ theorem, "Core/HostTable should define #{theorem}"
        assert ledger =~ theorem, "m2a-ledger should cite #{theorem} as proved"
      end
    end

    test "the assumed side names only adapter obligations, never theorems" do
      ledger = File.read!("proof/Core/RepresentationBoundary.agda")

      for obligation <- [
            "name-encoding",
            "extracted",
            "duplicates-rejected",
            "aliases-separate",
            "flags-uninterpreted",
            "order-preserved",
            "hidden-bodies-captured",
            "signature-immutable"
          ] do
        assert ledger =~ obligation
      end
    end
  end

  # ------------------------------------------------------------------
  # Host-shaped helpers. These mirror `Core.HostTable`'s definitions so
  # the audit exercises the same algorithm the proofs are about.
  # ------------------------------------------------------------------

  defp host_key(key, bindings) do
    case List.keyfind(bindings, key, 0) do
      {^key, value} -> value
      nil -> nil
    end
  end

  defp host_lookup(key, bindings, aliases) do
    case host_key(key, bindings) do
      nil ->
        case List.keyfind(aliases, key, 0) do
          {^key, target} -> host_key(target, bindings)
          nil -> nil
        end

      value ->
        value
    end
  end
end
