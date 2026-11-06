# M4b — Fuel adequacy: exact implementation plan

Status: **step 1 attempted and REFUTED.** See §8. The plan below is kept
as written so the error stays visible; the refutation is the operative
conclusion. Nothing from the attempt was kept; the tree is unchanged and
`./proof/check.sh` is green.

Prepared after the M4b investigation recorded in `proof/NEXT-STEPS.md` and
`Core.FailureImpossibility`'s `UnboundInversion`.

## 1. The goal, stated exactly

Prove, for the modelled evaluator:

```agda
adequate : ∀ {residual mode env term value} (d : Evaluates env term value)
  → run-config residual mode (height d) term env ≡ done (value , d)
```

i.e. **every finite derivation fits in fuel equal to its own height**, and
the worker returns that derivation's own value and evidence. Composed with
`Proof.ClosureEvaluation.evaluate` (derivation ⇒ native reduction), this
closes the chain *worker run ⇒ native reduct* for the modelled slice.

`PLAN.md` §9 states it as: "If model fuel is used, derive an adequate
height from the finite derivation; do not equate it to the executable
delta counter."

## 2. Why the current interface blocks it

`Core.ClosureEval` declares:

```agda
e-var : ∀ {k v} → lookup-value env k ≡ just v → Evaluates env (tm-var k) v
```

The lookup equation is **inside** the evidence. The worker's clause is:

```agda
run-config … (tm-var k) env with lookup-value env k in found
... | nothing    = stop unbound
... | just value = done (value , e-var found)
```

Two consequences, both verified by probe:

1. **The clause is irreducible at an abstract `k`.** `in found` is
   necessary (it supplies `e-var`'s premise), but it makes the clause
   stuck: at abstract `k` it evaluates to its `nothing` branch even with a
   `lookup-value env k ≡ just v` hypothesis in scope.
2. **`subst`/`rewrite` cannot transport an external equation in.** The
   goal's `done (value , e-var found)` and the caller's
   `done (v , e-var eq)` are equal only if `found` and `eq` are the *same
   proof object* — which needs proof irrelevance on `Maybe Value`
   equations, which this development deliberately does not assume.

The M5a design avoided this by making the policy's result and the visible
body the same term by construction. M4b cannot do that, because the
evidence is part of the *result type*.

## 3. The migration

### 3.1 The change

Replace the equation-carrying constructor with an equation-free one:

```agda
-- BEFORE
e-var : ∀ {k v} → lookup-value env k ≡ just v → Evaluates env (tm-var k) v

-- AFTER
e-var : ∀ {k v} → Evaluates env (tm-var k) v
```

The variable's value is no longer recoverable from the evidence. That is
the point: the derivation says *a* value exists, and the worker supplies
it. Callers that need the equation recover it from the environment
relation they already carry (`Environments`, `EnvironmentScoped`), which
is where it belongs.

### 3.2 The worker clause becomes reducible

```agda
run-config residual mode (suc fuel) (tm-var k) env with lookup-value env k
... | nothing    = stop unbound
... | just value = done (value , e-var)
```

No `in found`, so the clause reduces at a concrete decision and
`adequate` can rewrite with an external equation.

### 3.3 Consumer migration — exactly TWO sites

Verified by `grep`: `e-var` appears in only two consumers outside
`ClosureEval` itself.

| Site | Current | After |
|---|---|---|
| `Core/ClosureScope.agda:103` | `evaluate-scoped env (sc-var inside) (E.e-var found) = lookup-scoped env found` | `evaluate-scoped env (sc-var inside) E.e-var = lookup-scoped-at env inside` |
| `Proof/ClosureEvaluation.agda:130` | `evaluate env (E.e-var found) with lookup-denotation env found` | `evaluate env E.e-var with lookup-denotation-at env k` |

Both sites already have the environment relation (`EnvironmentScoped d env`,
`Environments d env terms`) and the index `k` in scope, so the equation is
recoverable. `lookup-scoped` and `lookup-denotation` keep their current
signatures; the call sites obtain the equation from the relation instead
of from the evidence.

**The one new obligation**: each consumer must derive
`lookup-value env k ≡ just value` from its environment relation *and* the
index. Both relations are length-indexed lists parallel to `env`, so this
is a short induction — the same shape as the existing `lookup-scoped` /
`lookup-denotation` bodies, just hoisted one level so the equation is a
result rather than an input.

Concretely, add to each consumer's module:

```agda
-- Core/ClosureScope
lookup-scoped-eq : ∀ {d env k} → EnvironmentScoped d env
  → ∃ λ value → lookup-value env k ≡ just value
```

and use it to discharge both the equation and the scope obligation.

### 3.4 What does NOT change

- `Evaluates`'s other constructors: unchanged.
- `Applies`, `EvaluatesSpine`: unchanged.
- `run-config`'s other clauses: unchanged.
- The `Failure` vocabulary: unchanged.
- `Core.FailureImpossibility`: its `e-var`-related comment must be
  updated, and `UnboundInversion` becomes **dischargeable** — that is a
  bonus, not a prerequisite.

## 4. Proof structure for `adequate`

```agda
mutual
  height : ∀ {env term value} → Evaluates env term value → ℕ
  -- one unit per node, `_⊔_` over children (they run SEQUENTIALLY at the
  -- same fuel, so the budget covers the tallest, not the sum)
```

`_⊔_` rather than `_+_` is deliberate: it is the derivation's actual
depth, which is what the worker counts. Using the sum would be sound but
would not be the honest measure.

### 4.1 The monotonicity lemma — the real work

The worker at `suc f` runs children at `f`, but `height` gives a child
`h_child ≤ f`. So the proof needs:

```agda
mono : ∀ {residual mode env term value} (d : Evaluates env term value)
  → ∀ {n m} → n ≤ m
  → run-config residual mode n term env ≡ done (value , d)
  → run-config residual mode m term env ≡ done (value , d)
```

proved by **mutual induction** over `Evaluates`/`Applies`/`EvaluatesSpine`.
This is the substantial part of M4b — roughly the size of
`Proof.ClosureEvaluation`'s `evaluate`.

Two cases need care:

- **`tm-data`** dispatches on `Layout.check-source`, which can reject.
  Handle by taking the accepted-layout evidence as a premise (as the M5a
  work learned to do) or by case on the layout result.
- **`case-config`** dispatches on `findBranch` and an arity comparison.
  Same treatment.

### 4.2 Then `adequate` follows

With `mono` available, each composite case rewrites the child's run at
`h_child` to a run at the parent's `fuel`, then the parent's clause fires.

## 5. Order of work

1. **Migrate `e-var`** (§3.1) and fix the two consumers (§3.3). Validate
   the full runner — this step alone should leave the tree green and is a
   reviewable checkpoint.
2. **Add `Core/FuelAdequacy.agda`** with `height` and `mono`. Validate.
3. **Add `adequate`** on top of `mono`. Validate.
4. **Discharge `UnboundInversion`** in `Core/FailureImpossibility` using
   the now-reducible clause. Validate.
5. **Compose** with `Proof.ClosureEvaluation.evaluate` into a single
   statement: a derivation at height `n` runs at fuel `n` and its result
   denotes a native reduct.
6. Update `proof/README.md`, `proof/NEXT-STEPS.md`, `docs/SOUNDNESS.md`.

Steps 1 and 2 are the risky ones; 3–5 are mechanical once `mono` exists.

## 6. Risks and stop conditions

- **Risk: `mono` is larger than expected.** It is a full mutual induction
  over three relations. If it grows past ~300 lines, stop and reassess
  whether `adequate` should instead be stated directly (by induction on
  the derivation, with the fuel bound derived per-node) rather than via
  `mono`.
- **Risk: a third `e-var` consumer exists.** The grep found two; re-run
  `grep -rn "e-var" --include=*.agda .` before starting and confirm.
- **STOP if** any step needs a new postulate, proof irrelevance, or a
  termination override. None should: the migration removes an obligation
  rather than adding one.
- **STOP if** a consumer cannot recover the equation from its environment
  relation. That would mean the relation does not determine the
  environment, which would be a finding worth reporting rather than
  working around.

## 7. Validation

Every step: `./proof/check.sh`, `./proof/scripts/check-postulates.sh`,
`python3 proof/scripts/test_hygiene.py`,
`python3 proof/scripts/check-hygiene.py`, `bash -n` on the shell scripts,
`git diff --check`. At the end: strict Credo, `mix format
--check-formatted`, and the standalone artifact reproduction check.

The postulate inventory must remain exactly `funext` and `tree-decides`.

## 8. OUTCOME — step 1 was attempted and refuted

§3.1 and §3.2 were implemented. The migration does not work, and the reason
is a property of the model rather than a gap in the proof. **§3.1's premise
and §3.2's claim are both wrong.**

### 8.1 `e-var` without its equation stops determining the value

With

```agda
e-var : ∀ {k v} → Evaluates env (tm-var k) v
```

the constructor has no premise at all, so it inhabits `Evaluates env
(tm-var k) v` for **every** `v`. Verified by probe:

```agda
any-value : ∀ {env k} (v : Value) → Evaluates env (tm-var k) v
any-value v = e-var          -- checks
```

So `Evaluates` no longer determines *which* value a variable evaluates to.
This is not something a better induction gets around: the relation itself
lost the information.

Both consumers must *produce* the value, so both fail:

| Consumer | Needs | Available after the change |
|---|---|---|
| `ClosureScope.evaluate-scoped` | `ValueScoped d value` for the value the derivation produced | the relation fixes a value; `e-var` no longer says the derivation used it |
| `ClosureEvaluation.evaluate` | `∃ term → Denotes d value term` | same |

`evaluate-scoped`'s goal is `ValueScoped d value` at `e-var`'s *implicit*
`value`, now unconstrained. A helper deriving `lookup-value env k ≡ just v`
from `EnvironmentScoped` was written and does typecheck — but Agda cannot
unify the value the relation determines with the one the goal mentions,
because nothing connects them any more. That is precisely the finding §6
asked to be reported rather than worked around.

### 8.2 §3.2 is inverted: the plain `with` cannot build `e-var`

§3.2 claims that with `e-var` equation-free the worker no longer needs `in
found`. True, but useless: the *equation itself* then becomes unreachable.
Probe, `e-var` still carrying its equation, clause written without `in`:

```agda
run (suc fuel) (tm-var k) env with lookup-value env k
... | nothing = stop
... | just v  = done (v , e-var {!!})     -- hole is UNSOLVABLE
```

`with` abstracts the scrutinee, so inside the `just v` branch Agda has no
`lookup-value env k ≡ just v`. `in found` is what supplies it — and `in
found` is exactly what makes the clause irreducible at an abstract index.
The two requirements are one requirement seen from both sides:

> A worker clause can produce `e-var`'s equation only by abstracting over
> it, and abstracting over it is exactly what blocks adequacy.

Making the field irrelevant (`.lookup-value env k ≡ just v`) does not help:
the problem is the *existence* of the equation, not its identity. Verified
by probe.

### 8.3 Why §2's diagnosis was incomplete

§2 blamed consequence 2 (the equation living inside the evidence) and
treated consequence 1 (`in found`) as its symptom. The probes show they are
independent: removing the equation from the evidence does not remove the
need for `in found`, it only removes the worker's ability to *use* it.

### 8.4 What this means for M4b

`UnboundInversion` stays a recorded limitation and fuel adequacy for
`run-config` is **not** reachable by this route. A future attempt needs one
of:

1. **A different worker shape** that does not return `Evaluates` evidence at
   all — e.g. a fuel-indexed evaluator returning only values, with a
   separate soundness theorem relating it to `Evaluates`. The equation then
   never has to be produced inside a `with`. This is the only option
   consistent with the standing constraints.
2. Proof irrelevance on `Maybe`-equations, which this development
   deliberately does not assume and §6 forbids introducing.
3. §4's `height`/`mono` structure, but against a worker other than
   `run-config`.

Option 1 is a redesign of the worker, not a migration of it, and should be
scoped as its own milestone rather than folded into M4b.

### 8.5 State of the tree

`Core/ClosureEval.agda` and `Core/ClosureScope.agda` are unmodified and
typecheck. The probes are four throwaway modules, reproduced below so the
refutation is auditable without trusting this prose. Each needs only
`standard-library`:

| Probe | Claim | Agda result |
|---|---|---|
| **A** | equation-free `e-var` admits every value | checks |
| **B** | plain `with` cannot build `e-var` | hole unsolvable |
| **C** | an irrelevant equation field does not help | hole unsolvable |
| **D** | `with … in found` works (the status quo) | checks |

Probe **A**:

```agda
data Evaluates (env : List Value) : Term → Value → Set where
  e-var : ∀ {k v} → Evaluates env (tm-var k) v
any-value : ∀ {env k} (v : Value) → Evaluates env (tm-var k) v
any-value v = e-var
```

Probes **B**/**C** are the same module differing only in the constructor's
premise (`lookup-value env k ≡ just v` vs `.lookup-value env k ≡ just v`)
and in the worker clause:

```agda
run (suc fuel) (tm-var k) env with lookup-value env k
... | nothing = stop
... | just v  = done (v , e-var {!!})
```

Probe **D** is **B** with the clause restored to the shipped shape:

```agda
run (suc fuel) (tm-var k) env with lookup-value env k in found
... | nothing = stop
... | just v  = done (v , e-var found)
```
