defmodule Cure.Elab.ConformanceSkeletonSelfOverlapTest do
  @moduledoc """
  Red→green for self-overlap in `Program.module_conformance_skeleton/3`.

  The conformance phase re-reads a module's source and registers its authored
  `implementation` declarations into a base environment assembled from the input
  skeletons and that module's resolved imports. Those imports can hand the
  module its OWN instance back: `Std.Char` declares `Equatable for Char` and
  `use`s `Std.Equatable`, whose whole-module `@prelude` slice keeps coherence
  intact — so once `Std.Char` has been published, its instance is ambient in the
  very environment its own re-registration lands in, and the module is reported
  as overlapping with itself.

  The signature phase already guards against exactly this by returning
  `%{signature | coherence: nil}`, and the body phase guards against it in
  `strip_shadowed_prelude_instances/2`. The conformance phase between them did
  not, so every warm stdlib build failed with
  `{:overlapping_instance, %{interface: :Equatable, head: :"Std.Char#Char"}}`.

  A module colliding with ITSELF is not an overlap. A module colliding with a
  FOREIGN instance for the same head still is — global coherence must survive
  the fix, which is what the second test pins.
  """
  use ExUnit.Case, async: true

  alias Cure.Core.Env
  alias Cure.Elab.{Coherence, Program}

  @path "lib/std/char.cure"
  @module "Std.Char"
  @head :"Std.Char#Char"

  defp signature_skeleton do
    {:ok, types} = Program.module_type_skeleton(@module, @path)
    {:ok, signature} = Program.module_signature_skeleton(@module, @path, [{@module, types}])
    signature
  end

  # `Std.Char`'s own `Equatable for Char`, with its method global mangled the way
  # its own registration mangles it: owner-qualified with `Std.Char`.
  defp own_instance_ref do
    %{
      iface: :Equatable,
      head: @head,
      methods: %{:== => :"Std.Char#__impl_Equatable_Std.Char#Char_=="},
      as: nil
    }
  end

  # The same `(interface, head)` provided by a DIFFERENT module -- a genuine
  # global-coherence violation.
  defp foreign_instance_ref do
    %{
      iface: :Equatable,
      head: @head,
      methods: %{:== => :"Other.Module#__impl_Equatable_Std.Char#Char_=="},
      as: nil
    }
  end

  defp skeleton_with(ref) do
    {:ok, coherence} =
      Coherence.register_anon(Coherence.new(), :Equatable, @head, ref, %{for: "Char"})

    Env.put_coherence(signature_skeleton(), coherence)
  end

  test "the module's own ambient instance does not collide with its declaration" do
    assert {:ok, env} =
             Program.module_conformance_skeleton(@module, @path, [
               {@module, skeleton_with(own_instance_ref())}
             ])

    assert Map.has_key?(env.coherence.anon, {:Equatable, @head}),
           "the authored instance must still be registered, not merely skipped"
  end

  test "a foreign instance for the same head is still an overlap" do
    assert {:error, {:overlapping_instance, %{interface: :Equatable, head: @head}}} =
             Program.module_conformance_skeleton(@module, @path, [
               {@module, skeleton_with(foreign_instance_ref())}
             ])
  end
end
