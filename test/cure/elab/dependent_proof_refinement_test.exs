defmodule Cure.Elab.DependentProofRefinementTest do
  use ExUnit.Case, async: true

  alias Cure.Elab.Program

  @added_preamble """
    type Bool = False | True
    type ListNat = Nil | Cons(Nat, ListNat)

    fn plus(left: Nat, right: Nat) -> Nat = match left
      Z() -> right
      S(previous) -> S(plus(previous, right))

    type Added indices (lefts: ListNat, rights: ListNat, results: ListNat)
      AddedNil : Added(Nil(), Nil(), Nil())
      AddedCons : (left: Nat) -> (right: Nat) -> Added(lefts, rights, results) -> Added(Cons(left, lefts), Cons(right, rights), Cons(plus(left, right), results))
  """

  defp added_module(body), do: "mod AddedRefinement\n  type Nat = Z | S(Nat)\n" <> @added_preamble <> body <> "end\n"

  test "AddedCons refinement composes beneath an earlier independent match" do
    source =
      added_module("""
        fn rebuild(flag: Bool, lefts: ListNat, rights: ListNat, results: ListNat,
          proof: Added(lefts, rights, results)) -> Added(lefts, rights, results) = match flag
          False() -> match proof
            AddedNil() -> AddedNil()
            AddedCons(left, right, rest) -> AddedCons(left, right, rest)
          True() -> match proof
            AddedNil() -> AddedNil()
            AddedCons(left, right, rest) -> AddedCons(left, right, rest)
      """)

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "constructor-fixed values, existential names, and sibling shapes reach the branch" do
    source =
      added_module("""
        type NonEmpty indices (values: ListNat)
          IsNonEmpty : NonEmpty(Cons(value, rest))

        fn head_sum(lefts: ListNat, rights: ListNat, results: ListNat,
          proof: Added(lefts, rights, results), sibling: NonEmpty(results)) -> Nat = match proof
          AddedNil() -> match sibling
            IsNonEmpty() -> impossible
          AddedCons(left, right, rest) -> match sibling
            IsNonEmpty() -> plus(left, right)
      """)

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "coverage prunes a constructor contradicted by concrete indices" do
    source =
      added_module("""
        fn only_empty(proof: Added(Nil(), Nil(), Nil())) -> Nat = match proof
          AddedNil() -> Z()
      """)

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "a stuck constructor-index equation remains available for reconstruction" do
    source = """
    mod ResidualIndexEvidence
      type Nat = Z | S(Nat)
      type ListNat = Nil | Cons(Nat, ListNat)
      fn append(left: ListNat, right: ListNat) -> ListNat = match left
        Nil() -> right
        Cons(head, tail) -> Cons(head, append(tail, right))
      type Split indices (values: ListNat)
        Empty : Split(Nil())
        Joined : Split(left) -> Split(right) -> Split(append(left, right))

      fn rebuild({left: ListNat}, {right: ListNat}, value: Split(append(left, right))) -> Split(append(left, right)) = match value
        Empty() -> Empty()
        Joined(first, second) -> Joined(first, second)
    end
    """

    assert {:ok, _env} = Program.elaborate(source)
  end

  test "residual evidence cannot justify a false sibling shape" do
    source = """
    mod ResidualIndexSoundness
      type Nat = Z | S(Nat)
      type ListNat = Nil | Cons(Nat, ListNat)
      fn append(left: ListNat, right: ListNat) -> ListNat = match left
        Nil() -> right
        Cons(head, tail) -> Cons(head, append(tail, right))
      type Split indices (values: ListNat)
        Empty : Split(Nil())
        Joined : Split(left) -> Split(right) -> Split(append(left, right))

      fn bad({left: ListNat}, {right: ListNat}, value: Split(append(left, right))) -> Split(append(left, right)) = match value
        Empty() -> Empty()
        Joined(first, second) -> Joined(second, first)
    end
    """

    assert {:error, _reason} = Program.elaborate(source)
  end

  test "a wrong dependent branch reports its authored pattern and dependent origin" do
    source =
      added_module("""
        fn bad(lefts: ListNat, rights: ListNat, results: ListNat,
          proof: Added(lefts, rights, results)) -> Added(lefts, rights, results) = match proof
          AddedNil() -> AddedNil()
          AddedCons(left, right, rest) -> AddedCons(right, left, rest)
      """)

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "dependent_branch.cure", emit_events: false)

    {diagnostic, registry} =
      Cure.Compiler.Errors.to_diagnostic(reason, "dependent_branch.cure", source)

    assert diagnostic.code == "E093"
    assert diagnostic.payload.kind == :branch_type
    assert diagnostic.payload.expectation_origin == :dependent_branch
    assert diagnostic.primary.span.start_line == 16
    assert diagnostic.primary.message =~ "incompatible"

    plain = Cure.Diagnostic.Renderer.plain(diagnostic)
    json = diagnostic |> Cure.Diagnostic.Renderer.json() |> Jason.decode!()
    lsp = Cure.Diagnostic.Renderer.lsp(diagnostic, registry, :utf16)
    assert plain =~ "constructor refines indices"
    assert json["payload"]["expectation_origin"] == "dependent_branch"
    assert lsp["code"] == "E093"
    assert lsp["range"]["start"]["line"] == 15
  end

  test "ordinary nondependent branch disagreements retain their existing origin" do
    source = """
    mod OrdinaryBranchMismatch
      type Choice = First | Second
      fn bad(choice: Choice) -> Nat = match choice
        First() -> Z()
        Second() -> First()
    end
    """

    assert {:error, {:codegen_error, reason}} =
             Cure.Compiler.compile_string(source, file: "ordinary_branch.cure", emit_events: false)

    {diagnostic, _registry} = Cure.Compiler.Errors.to_diagnostic(reason, "ordinary_branch.cure", source)
    assert diagnostic.code == "E093"
    assert diagnostic.payload.expectation_origin == :annotation
    assert diagnostic.title =~ "Pattern branches disagree"
  end
end
