defmodule Antigen.Generators.BetaSubstTest do
  use ExUnit.Case, async: true
  alias Antigen.Generators.BetaSubst
  alias Antigen.Backend.StreamData, as: B
  alias Antigen.{Challenge, Assays, Corpus}
  alias Antigen.Generators.SigMenu
  alias Cure.Core.{Normalise, Kernel}
  alias Cure.Elab.Subst

  @sample 200

  # A BROKEN substitution: it locates x (the variable at index `d` after crossing
  # `d` binders) but substitutes `e` WITHOUT shifting it — the capture bug correct
  # de Bruijn substitution avoids. Used to prove the capture traps have teeth.
  defp broke({:var, i}, e, d) do
    cond do
      i == d -> e
      i > d -> {:var, i - 1}
      true -> {:var, i}
    end
  end

  defp broke({:lam, _g, t, b}, e, d), do: {:lam, Cure.Core.Grade.unrestricted(), broke(t, e, d), broke(b, e, d + 1)}
  defp broke({:pi, _g, t, b}, e, d), do: {:pi, Cure.Core.Grade.unrestricted(), broke(t, e, d), broke(b, e, d + 1)}
  defp broke({:sigma, t, b}, e, d), do: {:sigma, broke(t, e, d), broke(b, e, d + 1)}
  # Inductive Sigma (D2): a `{:data, …}` node introduces no binder itself (its Σ
  # codomain lambda does, handled by the `{:lam}` clause), so its args recurse at the
  # same depth — required for the σ-shift trap to keep its teeth.
  defp broke({:data, n, ps, is}, e, d),
    do: {:data, n, Enum.map(ps, &broke(&1, e, d)), Enum.map(is, &broke(&1, e, d))}

  defp broke({:ctor, n, args}, e, d), do: {:ctor, n, Enum.map(args, &broke(&1, e, d))}
  defp broke({:app, f, x}, e, d), do: {:app, broke(f, e, d), broke(x, e, d)}

  defp broke({:case, s, m, brs}, e, d),
    do: {:case, broke(s, e, d), broke(m, e, d), Enum.map(brs, fn {c, a, b} -> {c, a, broke(b, e, d + a)} end)}

  defp broke(o, _e, _d), do: o

  defp ctx_of(types), do: SigMenu.rebuild_context(SigMenu.env_of(:v1), types)

  test "every sampled redex is a well-typed β-redex the kernel agrees on with subst" do
    for %Challenge{} = c <- B.interp(BetaSubst.gen()) |> Enum.take(@sample) do
      assert c.kind == :typed_term
      assert c.assay == "kernel/beta_subst"
      assert match?({:app, {:lam, _g, _, _}, _}, c.payload.term)

      assert match?({:ok, _}, Kernel.infer(ctx_of(c.payload.ctx), c.payload.term)),
             "redex not well-typed: #{c.note}"

      assert Assays.KernelLaw.run(c) == :ok, "β/subst disagreed on #{c.note}"
    end
  end

  # RED anchor: without the shift, every trap's naive substitution normalizes to a
  # DIFFERENT term than the kernel's β — so a shift/capture regression WOULD be
  # caught. (The correct assay above is the GREEN side.)
  test "each capture trap detects an unshifted substitution (reduction teeth)" do
    for {ctx_types, _type, t, e, body, note} <- BetaSubst.cases() do
      ctx = ctx_of(ctx_types)
      beta_nf = Normalise.nf(ctx, {:app, {:lam, Cure.Core.Grade.unrestricted(), t, body}, e})
      broken_nf = Normalise.nf(ctx, broke(body, e, 0))

      assert beta_nf != broken_nf,
             "capture trap #{note} does NOT distinguish an unshifted subst — no teeth"
    end
  end

  # The typing half validates the SUBSTITUTION LEMMA (Γ,x:A⊢b:B, Γ⊢e:A ⟹
  # Γ⊢b[e]:B[e]) — a property distinct from nf-agreement. Its capture teeth are
  # partial: a same-typed capture (var0 vs var1 both Nat, the `lam` traps) is
  # type-INVISIBLE and only the reduction half sees it; a type-relevant capture
  # (the Π/Σ traps, where an unshifted subst drops a Nat where a type is required)
  # is ill-typed and the typing half catches it. Assert both facts honestly.
  defp redex_type(ctx, t, e, body) do
    depth = Cure.Core.Context.length(ctx)
    {:ok, v} = Kernel.infer(ctx, {:app, {:lam, Cure.Core.Grade.unrestricted(), t, body}, e})
    Normalise.quote(v, depth)
  end

  defp broken_type(ctx, e, body) do
    depth = Cure.Core.Context.length(ctx)

    case Kernel.infer(ctx, broke(body, e, 0)) do
      {:ok, v} -> Normalise.quote(v, depth)
      {:error, _} -> :ill_typed
    end
  end

  test "the substitution lemma holds for every case (typing soundness)" do
    for {ctx_types, _type, t, e, body, note} <- BetaSubst.cases() do
      ctx = ctx_of(ctx_types)
      depth = Cure.Core.Context.length(ctx)
      {:ok, vr} = Kernel.infer(ctx, {:app, {:lam, Cure.Core.Grade.unrestricted(), t, body}, e})
      {:ok, vs} = Kernel.infer(ctx, Subst.instantiate(body, [e]))

      assert Normalise.quote(vr, depth) == Normalise.quote(vs, depth),
             "substitution lemma failed on #{note}"
    end
  end

  test "the typing half is non-vacuous: some trap's unshifted subst mis-types" do
    assert Enum.any?(BetaSubst.cases(), fn {ctx_types, _type, t, e, body, _note} ->
             ctx = ctx_of(ctx_types)
             broken_type(ctx, e, body) != redex_type(ctx, t, e, body)
           end),
           "no case exercises a type-relevant capture — the typing check is vacuous"
  end

  test "the menu spans lam depths 1–3, a Π/Σ codomain, and a case branch" do
    notes = BetaSubst.cases() |> Enum.map(&elem(&1, 5))

    for frag <- ["depth 1", "depth 2", "depth 3", "pi codomain", "sigma codomain", "case branch"] do
      assert Enum.any?(notes, &String.contains?(&1, frag)), "missing arm: #{frag}"
    end
  end

  test "every case round-trips through the corpus with its payload intact" do
    for {ctx, type, t, e, body, note} <- BetaSubst.cases() do
      chal =
        Challenge.new(
          kind: :typed_term,
          assay: "kernel/beta_subst",
          label: :well_typed,
          payload: %{sig: :v1, ctx: ctx, type: type, term: {:app, {:lam, Cure.Core.Grade.unrestricted(), t, body}, e}},
          note: note
        )

      line = Corpus.encode_record(chal)
      assert {:ok, c2} = Corpus.decode_record(line)
      assert c2.assay == "kernel/beta_subst"
      assert c2.payload.term == chal.payload.term
    end
  end
end
