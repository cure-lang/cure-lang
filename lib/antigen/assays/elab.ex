defmodule Antigen.Assays.Elab do
  @moduledoc """
  Elaborator completeness + metamorphic assays (property-based testing for the
  `Surface → Core` elaborator rather than the kernel).

    * elab/completeness — a construction-guaranteed well-typed surface program
      MUST elaborate. A `{:error, _}` is an infection: an unsound REJECT (a
      completeness / reach gap), the elaborator-layer analogue of an unsound
      accept. The kernel cannot catch this — it is behaving correctly when it
      rejects a mis-framed Core term the elaborator produced.

    * elab/metamorphic — a typing-preserving transform (α-rename, arm reorder,
      unused binder) MUST NOT change the accept/reject verdict. A divergence is
      an infection, evidence of a de Bruijn / binder-framing bug. This oracle is
      self-contained (no Idris): it compares the elaborator against itself.

    * elab/erasure — a TWO-SIDED pin on the `{0,ω}` relevance check
      (`Cure.Elab.Relevance`, M8.3). Catalog form: the actual accept/reject
      verdict must equal the expected one (so both an under-strict and an
      over-strict check infect). Metamorphic form: `:same` (frame perturbation —
      verdicts agree) or `:flip` (relevance injection — an accepting base must
      become a rejecting variant, proving the check is load-bearing).

  All consume an `:elab_program` challenge and return `:ok | {:violation, _}`.
  """
  alias Antigen.Challenge
  alias Cure.Elab.{Program, Erase}
  alias Cure.Core.{Kernel, Conv, Eval, Context}

  @assay_fuel 500_000
  @real_kernel %{
    elaborate: &Cure.Elab.Program.elaborate/1,
    infer: &Kernel.infer/2,
    check: &Kernel.check/3,
    conv: &Conv.conv_values?/4,
    eval: &Eval.eval/2
  }
  @doc false
  def __real_kernel__, do: @real_kernel

  @spec run(Challenge.t()) :: :ok | {:violation, term()}
  def run(%Challenge{kind: :elab_program, assay: "elab/completeness", payload: p}) do
    case elaborate(p.src) do
      {:ok, _} -> :ok
      {:error, e} -> {:violation, {:rejected_well_typed, p.id, e}}
      {:raise, e} -> {:violation, {:raised, p.id, e}}
    end
  end

  def run(%Challenge{kind: :elab_program, assay: "elab/metamorphic", payload: p}) do
    base = verdict_bit(elaborate(p.base_src))
    variant = verdict_bit(elaborate(p.variant_src))

    if base == variant do
      :ok
    else
      {:violation, {:verdict_not_invariant, p.id, p.transform, %{base: base, variant: variant}}}
    end
  end

  # elab/erasure — two-sided {0,ω} relevance-check pin. Catalog form: the actual
  # verdict must match the expected one (an under-strict OR over-strict check both
  # infect).
  def run(%Challenge{kind: :elab_program, assay: "elab/erasure", payload: %{expect: expect} = p}) do
    actual = verdict_bit(elaborate(p.src))

    if actual == expect do
      :ok
    else
      {:violation, {:erasure_verdict_wrong, p.id, %{expected: expect, actual: actual}}}
    end
  end

  # elab/erasure — metamorphic form. `:same` = base and variant verdicts must
  # agree (frame-preserving perturbation); `:flip` = an accepting base must become
  # a rejecting variant (the relevance injection is load-bearing).
  def run(%Challenge{kind: :elab_program, assay: "elab/erasure", payload: %{relation: rel} = p}) do
    base = verdict_bit(elaborate(p.base_src))
    variant = verdict_bit(elaborate(p.variant_src))

    ok? =
      case rel do
        :same -> base == variant
        :flip -> base == :accept and variant == :reject
      end

    if ok? do
      :ok
    else
      {:violation, {:erasure_relation_wrong, p.id, p.transform, %{relation: rel, base: base, variant: variant}}}
    end
  end

  # elab/dot_forcing — catalog form (spec 2026-07-08-antigen-elab-dot-forcing):
  # the actual verdict must match the expected one. Reject cells carrying
  # `expect_error` also pin the error HEAD, so a fixture that rots into
  # rejecting for an unrelated reason (parse error, unbound name) infects
  # instead of passing silently.
  def run(%Challenge{kind: :elab_program, assay: "elab/dot_forcing", payload: %{expect: expect} = p}) do
    result = elaborate(p.src)
    actual = verdict_bit(result)

    cond do
      actual != expect ->
        {:violation, {:dot_forcing_verdict_wrong, p.id, %{expected: expect, actual: actual}}}

      actual == :reject and Map.has_key?(p, :expect_error) ->
        got = reject_head(result)

        if got == p.expect_error do
          :ok
        else
          {:violation, {:dot_forcing_wrong_reject_reason, p.id, got}}
        end

      true ->
        :ok
    end
  end

  # elab/dot_forcing — relation form: `:same` (verdict invariant under a
  # typing-preserving perturbation) or `:flip` (an accepting base must reject
  # after the targeted mutation — the call-site-wiring / load-bearing pin).
  def run(%Challenge{kind: :elab_program, assay: "elab/dot_forcing", payload: %{relation: rel} = p}) do
    base = verdict_bit(elaborate(p.base_src))
    variant = verdict_bit(elaborate(p.variant_src))

    ok? =
      case rel do
        :same -> base == variant
        :flip -> base == :accept and variant == :reject
      end

    if ok? do
      :ok
    else
      {:violation, {:dot_forcing_relation_wrong, p.id, p.transform, %{relation: rel, base: base, variant: variant}}}
    end
  end

  # elab/guard_lint — catalog form (spec 2026-07-08-guard-coverage-lint §6):
  # hand-verified exhaustive/non-exhaustive labels, two-sided; reject cells pin
  # the error HEAD (:unsupported_guard) so a fixture that rots into rejecting
  # for an unrelated reason (parse error, unbound name) infects.
  def run(%Challenge{kind: :elab_program, assay: "elab/guard_lint", payload: %{expect: expect} = p}) do
    result = elaborate(p.src)
    actual = verdict_bit(result)

    cond do
      actual != expect ->
        {:violation, {:guard_lint_verdict_wrong, p.id, %{expected: expect, actual: actual}}}

      actual == :reject and Map.has_key?(p, :expect_error) ->
        got = reject_head(result)

        if got == p.expect_error do
          :ok
        else
          {:violation, {:guard_lint_wrong_reject_reason, p.id, got}}
        end

      true ->
        :ok
    end
  end

  # elab/guard_lint — relation form: `:same` (verdict invariant under a
  # typing-preserving perturbation) or `:flip` (dropping a guard from a
  # proven-exhaustive set must flip accept -> reject — the never-over-prove pin).
  def run(%Challenge{kind: :elab_program, assay: "elab/guard_lint", payload: %{relation: rel} = p}) do
    base = verdict_bit(elaborate(p.base_src))
    variant = verdict_bit(elaborate(p.variant_src))

    ok? =
      case rel do
        :same -> base == variant
        :flip -> base == :accept and variant == :reject
      end

    if ok? do
      :ok
    else
      {:violation, {:guard_lint_relation_wrong, p.id, p.transform, %{relation: rel, base: base, variant: variant}}}
    end
  end

  # elab/nat_rep — representation agreement (spec 2026-07-08-nat-int-erasure §3):
  # the kernel's certified-δ normalisation of `main` (inductive semantics; the
  # trusted oracle) must decode to the same integer BEAM execution returns
  # (Int-rep emit; the system under test). NOT Eval.eval/2 — that leaves
  # `{:global, _}` heads as stuck neutrals and cannot reduce `add(...)`.
  def run(%Challenge{kind: :elab_program, assay: "elab/nat_rep", payload: p}) do
    case elaborate(p.src) do
      {:ok, env} ->
        kernel = kernel_nat(env)
        beam = beam_nat(env, p)

        cond do
          match?({:stuck, _}, kernel) ->
            {:violation, {:nat_rep_kernel_stuck, p.id, elem(kernel, 1)}}

          match?({:failed, _}, beam) ->
            {:violation, {:nat_rep_beam_failed, p.id, elem(beam, 1)}}

          kernel != beam ->
            {:violation, {:nat_rep_mismatch, p.id, %{kernel: kernel, beam: beam}}}

          true ->
            :ok
        end

      other ->
        # `other` cannot be `{:ok, _}` here (already matched above), so
        # `verdict_bit(other)` would always be the tautological `:reject` —
        # carry the actual rejection term instead, so a real corpus regression
        # is debuggable rather than reporting a constant.
        {:violation, {:nat_rep_program_rejected, p.id, other}}
    end
  end

  # elab/soundness — the emitted core is independently re-checked by the trusted
  # kernel: every def the elaborator produced must type-check at its emitted type.
  def run(%Challenge{kind: :elab_program, assay: "elab/soundness"} = c),
    do: run(c, @real_kernel)

  def run(%Challenge{kind: :elab_program, assay: "elab/soundness", payload: p}, k) do
    case safe_elaborate(k, p.src) do
      {:ok, env} -> check_all_defs(env, k)
      # reject -> elab/completeness' job
      {:error, _} -> :ok
      {:raise, e} -> {:violation, {:elaborator_raised, p.id, e}}
    end
  end

  defp safe_elaborate(k, src) do
    case k.elaborate.(src) do
      {:ok, env} -> {:ok, env}
      {:error, e} -> {:error, e}
      other -> {:error, {:unexpected, other}}
    end
  rescue
    ex -> {:raise, Exception.message(ex)}
  catch
    kind, reason -> {:raise, {kind, reason}}
  end

  # Fold env.defs in a fixed key order; first infection wins (deterministic).
  defp check_all_defs(env, k) do
    ctx = Context.empty(env)

    env.defs
    |> Enum.sort_by(fn {name, _} -> name end)
    |> Enum.find_value(:ok, fn {name, %{type: ty, body: body}} ->
      if is_nil(body) or extern_body?(body) or Erase.has_hole?(body) do
        # skip body-less (builtin-op, K2) / extern FFI axiom / incomplete def —
        # none are kernel-checkable (the kernel has no clause for an extern body;
        # like a postulate, it is trusted at its declared type). Mirrors the
        # production pipeline's `extern_def?` skip in totality_closure.ex.
        nil
      else
        case Cure.Core.Normalise.with_fuel(@assay_fuel, fn -> check_one(k, ctx, name, ty, body) end) do
          :ok -> nil
          :fuel_exhausted -> {:violation, {:fuel_exhausted, name}}
          {:violation, _} = v -> v
        end
      end
    end)
  end

  # An `@extern(mod, fun, arity)` FFI body — a value-level axiom the kernel does
  # not inspect (there is no `infer` clause for it, by design).
  defp extern_body?({:extern, _}), do: true
  defp extern_body?(_), do: false

  # infer -> Conv (with a check-fallback for checking-mode-only forms, e.g.
  # parameter-bearing constructor bodies the kernel refuses to infer).
  defp check_one(k, ctx, name, ty, body) do
    case k.infer.(ctx, body) do
      {:error, {:ctor_requires_checking_mode, _}} ->
        # Introduction form the kernel only checks (parameter-bearing ctor, etc.):
        # check against the declared type. `check` re-derives the constructor's
        # actual family/args and Conv-compares internally, so a wrong annotation
        # is still caught.
        case k.check.(ctx, body, k.eval.(ty, [])) do
          :ok -> :ok
          {:error, e} -> {:violation, {:core_ill_typed, name, e}}
        end

      {:error, e} ->
        {:violation, {:core_ill_typed, name, e}}

      {:ok, inferred} ->
        ty_v = k.eval.(ty, [])

        if k.conv.(inferred, ty_v, Context.length(ctx), Context.signature(ctx)) do
          :ok
        else
          {:violation, {:type_annotation_wrong, name, %{inferred: inferred, declared: ty}}}
        end
    end
  end

  # Elaborate, normalizing a raised exception into a tagged value so a crash in
  # the elaborator counts as its own infection class rather than aborting the run.
  defp elaborate(src) do
    try do
      case Program.elaborate(src) do
        {:ok, env} -> {:ok, env}
        {:error, e} -> {:error, e}
        other -> {:error, {:unexpected, other}}
      end
    rescue
      ex -> {:raise, Exception.message(ex)}
    catch
      kind, reason -> {:raise, {kind, reason}}
    end
  end

  # Collapse an elaboration result to its accept/reject bit (metamorphic compares
  # only the bit, not the specific error — different arms may report different
  # errors while agreeing on rejection).
  defp verdict_bit({:ok, _}), do: :accept
  defp verdict_bit(_), do: :reject

  # Error head of a rejecting elaboration result. Non-tuple hardening (spec
  # §2.3): parser grammar failures carry a LIST, and a normalized raise has no
  # head — neither can ever match an `expect_error` atom, so both land in the
  # wrong-reject-reason violation instead of crashing `elem/2`.
  defp reject_head({:error, {:source_context, reason, _context}}),
    do: reject_head({:error, reason})

  defp reject_head({:error, e}) when is_tuple(e) and tuple_size(e) > 0, do: elem(e, 0)
  defp reject_head({:error, _non_tuple}), do: :non_tuple_error
  defp reject_head({:raise, _}), do: :raised_error

  # -- elab/nat_rep helpers ----------------------------------------------------

  defp kernel_nat(env) do
    ctx = Context.empty(env)

    case Cure.Core.Normalise.nf(ctx, {:global, :main}, delta: :certified, mode: :nf) do
      :fuel_exhausted -> {:stuck, :fuel_exhausted}
      term -> decode_nat(term)
    end
  end

  # Match on the constructor's BASE name (`Cure.Elab.Name.base/1`), so both the
  # bare `:Z`/`:S` spelling and the canonical owner-qualified `:"Std.Nat#Z"` /
  # `:"Std.Nat#S"` identity decode identically. The canonicalization pass makes
  # a declared family's own ctors canonical regardless of local shadowing, so
  # this corpus's `Nat` programs now normalize to the `#`-qualified atoms.
  defp decode_nat({:ctor, name, args}) do
    case {Cure.Elab.Name.base(name), args} do
      {"Z", []} ->
        {:nat, 0}

      {"S", [inner]} ->
        case decode_nat(inner) do
          {:nat, n} -> {:nat, n + 1}
          other -> other
        end

      _ ->
        {:stuck, {:ctor, name, args}}
    end
  end

  defp decode_nat(other), do: {:stuck, other}

  defp beam_nat(env, p) do
    mod_name = :"Antigen.NatRep.#{:erlang.phash2(p.id)}"

    case Cure.Elab.Emit.compile_and_load(env, module: mod_name, functions: p.functions) do
      {:ok, mod} ->
        case apply(mod, :main, []) do
          n when is_integer(n) -> {:nat, n}
          other -> {:failed, {:non_integer, other}}
        end

      err ->
        {:failed, err}
    end
  rescue
    e -> {:failed, {:raised, e}}
  end
end
