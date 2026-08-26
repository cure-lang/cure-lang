defmodule Cure.Elab.NamedImplicitTailTest do
  @moduledoc """
  Ledger row #5 tail (spec 2026-07-08-dotsyntax-tail-design): the three
  named-implicit caveats C-a / C-b / C-c. Each test names the caveat it pins.
  """
  use ExUnit.Case, async: true
  alias Cure.Elab.Program

  # Vec with an erased implicit index arg `n` on vcons. `{n = .k}` is a
  # named-implicit annotation on that erased slot.
  @preamble """
    type Nat = Z | S(Nat)
    type Vec(a: Type) indices (n: Nat)
      vnil : Vec(a, Z)
      vcons : a -> Vec(a, n) -> Vec(a, S(n))
  """

  defp mod(body), do: "mod P\n" <> @preamble <> body <> "end\n"

  describe "C-b: named-implicit patterns never reach expression position" do
    test "branch body referencing the scrutinee elaborates (refine_scrutinee_in_body site)" do
      src =
        mod("""
          fn f({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
            vcons({n = .k}, h, t) -> v
        """)

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "as-pattern over a named-implicit ctor pattern with body ref elaborates (strip_as_patterns site)" do
      src =
        mod("""
          fn g({a: Type}, {k: Nat}, v: Vec(a, S(k))) -> Vec(a, S(k)) = match v
            w @ vcons({n = .k}, h, t) -> w
        """)

      assert {:ok, _env} = Program.elaborate(src)
    end
  end

  # Carried + forced mixed shape: `H`'s FIRST index is ctor-pinned (forced:
  # matching `hmk` against `H(S(j), …)` pins `m := j`), while the SECOND is a
  # stuck function index carried via the sibling `w` (detect_carried_index).
  @carried_preamble """
    type SList = SNil | SCons(Nat, SList)
    fn app(xs: SList, ys: SList) -> SList = match xs
      SNil() -> ys
      SCons(h, t) -> SCons(h, app(t, ys))
    type H indices (n: Nat, xs: SList)
      hmk : H(S(m), app(as, bs))
    type G indices (xs: SList)
      gwrap : G(cs)
  """

  defp cmod(body),
    do: "mod P\n  type Nat = Z | S(Nat)\n" <> @carried_preamble <> body <> "end\n"

  describe "C-a: forced check runs on the carried-eq path" do
    test "wrong dot on a carried-eq branch rejects" do
      src =
        cmod("""
          fn f({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
            hmk({m = .(S(j))}) -> Z()
        """)

      assert {:error, {:forced_pattern_mismatch, _, _}} = semantic_elaborate(src)
    end

    test "right dot on a carried-eq branch accepts (over-rejection guard)" do
      src =
        cmod("""
          fn g({j: Nat}, {p: SList}, {q: SList}, v: H(S(j), app(p, q)), w: G(app(p, q))) -> Nat = match v
            hmk({m = .j}) -> Z()
        """)

      assert {:ok, _env} = Program.elaborate(src)
    end
  end

  describe "C-c prerequisite: Relevance polices erased ctor fields in match arms" do
    test "a branch body returning an erased ctor field is erased_used_relevantly" do
      # Box's ctor `bmk : Box(m)` has one field: the erased implicit `m`.
      src =
        mod("""
          type Box indices (n: Nat)
            bmk : Box(m)
        """)

      {:ok, env} = Program.elaborate(src)

      # Hand-built Core body for `fn f(b: Box(k)) -> Nat`: ONE outer param, the
      # present scrutinee `b` at var-index 0. Branch `bmk` binds 1 field (the
      # erased `m`) and RETURNS it — `{:var, 0}` under the branch's 1 fresh
      # binder. The motive slot is ignored by Relevance.walk.
      #
      # An all-`:unrestricted` signature is deliberate. §2.3's fold introduces the
      # erased binder from the PATTERN, not the signature, and `Relevance.check/4`
      # walks every body regardless of its own quantities, so this is policed
      # without needing a dummy erased top-level parameter to prime the walk.
      body = {:case, {:var, 0}, {:type, 0}, [{ctor_atom(env, :bmk), 1, {:var, 0}}]}

      assert {:error, {:erased_used_relevantly, %{site: :returned}}} =
               Cure.Elab.Relevance.check(env, :probe_fn, [:unrestricted], body)
    end
  end

  # The elaborated ctor name may be bare (`:bmk`) or namespaced (`:"P.bmk"`);
  # pick whichever `Inductive.ctor_quantities` actually resolves in this env.
  defp ctor_atom(env, base) do
    Enum.find([base, String.to_atom("P." <> to_string(base))], base, fn c ->
      is_list(Cure.Core.Inductive.ctor_quantities(env, c))
    end)
  end

  @exist_preamble """
    type Nat = Z | S(Nat)
    type Vec(a: Type) indices (n: Nat)
      vnil : Vec(a, Z)
      vcons : a -> Vec(a, n) -> Vec(a, S(n))
    type Pack(a: Type) indices ()
      pk : Vec(a, m) -> Pack(a)
  """

  defp emod(body), do: "mod P\n" <> @exist_preamble <> body <> "end\n"

  describe "C-c: unforced bare-variable named implicits bind at quantity 0" do
    test "binding accepted when used only erasedly" do
      src =
        emod("""
          fn f({a: Type}, p: Pack(a)) -> Nat = match p
            pk({m = mm}, v) -> Z()
        """)

      assert {:ok, _env} = Program.elaborate(src)
    end

    test "relevant use of the bound variable rejects via Relevance" do
      src =
        emod("""
          fn g({a: Type}, p: Pack(a)) -> Nat = match p
            pk({m = mm}, v) -> mm
        """)

      assert {:error, {:erased_used_relevantly, _}} = semantic_elaborate(src)
    end

    test "dot form on an unforced position still errors" do
      src =
        emod("""
          fn h({a: Type}, p: Pack(a)) -> Nat = match p
            pk({m = .(S(Z()))}, v) -> Z()
        """)

      assert {:error, {:named_implicit_unforced, "m"}} = semantic_elaborate(src)
    end
  end

  test "a forced relevant implicit can still be pattern-bound as a value" do
    src = """
    mod ForcedRelevantImplicit
      type Nat = Z | S(Nat)
      type Indexed indices (index: Nat)
        MkIndexed : {value: Nat} -> Indexed(value)

      fn reveal({index: Nat}, item: Indexed(index)) -> Nat = match item
        MkIndexed({value = revealed}) -> revealed
    end
    """

    assert {:ok, _env} = Program.elaborate(src)
  end

  defp semantic_elaborate(src) do
    case Program.elaborate(src) do
      {:error, error} -> {:error, Program.semantic_error(error)}
      result -> result
    end
  end
end
