defmodule Cure.Elab.ProofSearchRegistryTest do
  use ExUnit.Case, async: true
  alias Cure.Core.Env

  test "put_lemma files an entry under its conclusion head and lemmas/2 retrieves it" do
    entry = %{name: :"M#lem", type: {:data, :"M#IsPositive", [], []}, arity: 2}
    env = Env.put_lemma(Env.empty(), :"M#IsPositive", entry)

    assert Env.lemmas(env, :"M#IsPositive") == [entry]
    assert Env.lemmas(env, :"M#Other") == []
  end

  test "put_lemma accumulates multiple lemmas under the same head" do
    a = %{name: :"M#a", type: {:data, :"M#P", [], []}, arity: 0}
    b = %{name: :"M#b", type: {:data, :"M#P", [], []}, arity: 1}

    env =
      Env.empty()
      |> Env.put_lemma(:"M#P", a)
      |> Env.put_lemma(:"M#P", b)

    assert Env.lemmas(env, :"M#P") == [a, b]
  end
end

defmodule Cure.Elab.LemmaCrossModuleMergeTest do
  use ExUnit.Case, async: false

  alias Cure.Elab.Program

  # `use`-importing a module must preserve @lemma-tagged theorems registered in
  # it — Task 9 relies on this (Std.Refine's hole must see Std.Proof.Math's
  # tagged lemma). `merge_env/2` is a private function of `Program`, so the
  # only way to genuinely exercise the merge path (rather than asserting on an
  # unmerged env, which is trivially true by construction and proves nothing
  # about merging) is to drive a real `use` through `Program.elaborate/1`
  # across two on-disk modules, mirroring the canonical cross-module loader
  # test pattern used elsewhere in this suite.
  setup do
    root = Path.join(System.tmp_dir!(), "cure_lemma_merge_test_#{System.unique_integer([:positive])}")
    File.mkdir_p!(root)
    previous_roots = Process.get(:cure_source_roots)
    Process.put(:cure_source_roots, [root])

    on_exit(fn ->
      if previous_roots,
        do: Process.put(:cure_source_roots, previous_roots),
        else: Process.delete(:cure_source_roots)

      File.rm_rf!(root)
    end)

    {:ok, root: root}
  end

  test "a lemma registered in a REAL used module (disk-loaded, via genuine `use`) survives merge_env into the importer",
       %{root: root} do
    write_module(root, "base.cure", "ProbeLemma.Base", """
    type P indices ()
      MkP : P()

    @lemma
    fn fact() -> P() = MkP()
    """)

    assert {:ok, env} =
             Program.elaborate("""
             mod ProbeLemma.Main
               use ProbeLemma.Base

               fn needs_p() -> P() = ?
             end
             """)

    all_entries = env.lemmas |> Map.values() |> List.flatten()

    assert Enum.any?(all_entries, fn e -> Atom.to_string(e.name) |> String.ends_with?("fact") end),
           "expected the Base module's @lemma to survive merge_env into Main, got: #{inspect(env.lemmas)}"
  end

  defp write_module(root, file, module_name, body) do
    path = Path.join(root, file)
    File.write!(path, "mod #{module_name}\n  #{body}\nend\n")
    path
  end
end
