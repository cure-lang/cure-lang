------------------------------------------------------------------------
-- Residual forms permit administrative congruence, never computational
-- roots. Provenance is stronger than mere equality of step endpoints.
------------------------------------------------------------------------
module Proof.ResidualNormal where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Core.Syntax
open import Core.Signature using (nothing≠just)
open import Core.Reduction
import Core.ResidualNormal as N
import Core.ClosureQuote as Q

module Administrative (sig : Signature) where
  mutual
    data Step : ∀ {t u} → _⇝_ sig t u → Set where
      a-app₁ : ∀ {f f′ a} {s : _⇝_ sig f f′} → Step s → Step (ξ-app₁ {a = a} s)
      a-app₂ : ∀ {f a a′} {s : _⇝_ sig a a′} → Step s → Step (ξ-app₂ {f = f} s)
      a-pi-dom : ∀ {g d d′ b} {s : _⇝_ sig d d′} → Step s → Step (ξ-pi-dom {g = g} {b = b} s)
      a-pi-cod : ∀ {g d b b′} {s : _⇝_ sig b b′} → Step s → Step (ξ-pi-cod {g = g} {d = d} s)
      a-lam-dom : ∀ {g d d′ b} {s : _⇝_ sig d d′} → Step s → Step (ξ-lam-dom {g = g} {b = b} s)
      a-lam-body : ∀ {g d b b′} {s : _⇝_ sig b b′} → Step s → Step (ξ-lam-body {g = g} {d = d} s)
      a-ctor : ∀ {name args x′} {i : Fin (len args)} {s : _⇝_ sig (lookupAt args i) x′}
        → Step s → Step (ξ-ctor-at {n = name} {args = args} i s)
      a-data-params : ∀ {name ps is x′} {i : Fin (len ps)} {s : _⇝_ sig (lookupAt ps i) x′}
        → Step s → Step (ξ-data-params-at {n = name} {is = is} {ps = ps} i s)
      a-data-indices : ∀ {name ps is x′} {i : Fin (len is)} {s : _⇝_ sig (lookupAt is i) x′}
        → Step s → Step (ξ-data-indices-at {n = name} {ps = ps} {is = is} i s)
      a-case : ∀ {s s′ m branches} {step : _⇝_ sig s s′}
        → Step step → Step (ξ-case {m = m} {brs = branches} step)
      a-motive : ∀ {s m m′ branches} {step : _⇝_ sig m m′}
        → Step step → Step (ξ-case-motive {s = s} {brs = branches} step)
      a-branches : ∀ {s m bs bs′} {steps : _⇝*ᵇ_ sig bs bs′}
        → BranchPath steps → Step (ξ-case-brs {s = s} {m = m} steps)
    data Path : ∀ {t u} → _⇝*_ sig t u → Set where
      a-refl : ∀ {t} → Path (⇝*-refl {t = t})
      a-step : ∀ {t u v} {s : _⇝_ sig t u} {ss : _⇝*_ sig u v}
        → Step s → Path ss → Path (⇝*-step s ss)
    data BranchPath : ∀ {bs bs′} → _⇝*ᵇ_ sig bs bs′ → Set where
      a[] : BranchPath ⇝ᵇ-nil
      a∷ : ∀ {name ar b b′ bs bs′} {s : _⇝*_ sig b b′} {ss : _⇝*ᵇ_ sig bs bs′}
        → Path s → BranchPath ss → BranchPath (⇝ᵇ-cons {cn = name} {ar = ar} s ss)

  mutual
    step-identity : ∀ {t u} {s : _⇝_ sig t u} → Step s → t ≡ u
    step-identity (a-app₁ proof) = cong (λ f → tm-app f _) (step-identity proof)
    step-identity (a-app₂ proof) = cong (tm-app _) (step-identity proof)
    step-identity (a-pi-dom proof) = cong (λ d → tm-pi _ d _) (step-identity proof)
    step-identity (a-pi-cod proof) = cong (tm-pi _ _) (step-identity proof)
    step-identity (a-lam-dom proof) = cong (λ d → tm-lam _ d _) (step-identity proof)
    step-identity (a-lam-body proof) = cong (tm-lam _ _) (step-identity proof)
    step-identity (a-ctor {args = args} {i = i} proof) =
      cong (tm-ctor _) (terms-identity args i (step-identity proof))
    step-identity (a-data-params {ps = ps} {i = i} proof) =
      cong (λ xs → tm-data _ xs _) (terms-identity ps i (step-identity proof))
    step-identity (a-data-indices {is = is} {i = i} proof) =
      cong (tm-data _ _) (terms-identity is i (step-identity proof))
    step-identity (a-case proof) = cong (λ s → tm-case s _ _) (step-identity proof)
    step-identity (a-motive proof) = cong (λ m → tm-case _ m _) (step-identity proof)
    step-identity (a-branches proof) = cong (tm-case _ _) (branches-identity proof)
    path-identity : ∀ {t u} {ss : _⇝*_ sig t u} → Path ss → t ≡ u
    path-identity a-refl = refl
    path-identity (a-step head tail) = trans (step-identity head) (path-identity tail)
    branches-identity : ∀ {bs bs′} {ss : _⇝*ᵇ_ sig bs bs′} → BranchPath ss → bs ≡ bs′
    branches-identity a[] = refl
    branches-identity (a∷ {name} {ar} head tail) =
      cong₂ _∷_ (cong (λ b → name , ar , b) (path-identity head)) (branches-identity tail)
    terms-identity : ∀ args (i : Fin (len args)) {x′} → lookupAt args i ≡ x′ → args ≡ setAt args i x′
    terms-identity (x ∷ xs) zero equal = cong (_∷ xs) equal
    terms-identity (x ∷ xs) (suc i) equal = cong (x ∷_) (terms-identity xs i equal)

  mutual
    normal-step : ∀ {t u} → N.Normal sig t → (step : _⇝_ sig t u) → Step step
    normal-step N.nf-type ()
    normal-step N.nf-atom-type ()
    normal-step N.nf-atom ()
    normal-step (N.nf-pi domain body) (ξ-pi-dom step) = a-pi-dom (normal-step domain step)
    normal-step (N.nf-pi domain body) (ξ-pi-cod step) = a-pi-cod (normal-step body step)
    normal-step (N.nf-lam domain body) (ξ-lam-dom step) = a-lam-dom (normal-step domain step)
    normal-step (N.nf-lam domain body) (ξ-lam-body step) = a-lam-body (normal-step body step)
    normal-step (N.nf-ctor fields) (ξ-ctor-at i step) = a-ctor (terms-step fields i step)
    normal-step (N.nf-data params indices) (ξ-data-params-at i step) = a-data-params (terms-step params i step)
    normal-step (N.nf-data params indices) (ξ-data-indices-at i step) = a-data-indices (terms-step indices i step)
    normal-step (N.nf-neutral head) step = neutral-step head step
    neutral-step : ∀ {t u} → N.Residual sig t → (step : _⇝_ sig t u) → Step step
    neutral-step N.ne-var ()
    neutral-step (N.ne-global opaque-body) (δ found) = ⊥-elim (nothing≠just (trans (sym opaque-body) found))
    neutral-step (N.ne-app () argument) β
    neutral-step (N.ne-app function argument) (ξ-app₁ step) = a-app₁ (neutral-step function step)
    neutral-step (N.ne-app function argument) (ξ-app₂ step) = a-app₂ (normal-step argument step)
    neutral-step (N.ne-case () motive branches) (ι found arity)
    neutral-step (N.ne-case () motive branches) (ι-nat-zero found arity)
    neutral-step (N.ne-case () motive branches) (ι-nat-suc found arity)
    neutral-step (N.ne-case () motive branches) (ι-bounded-zero found arity)
    neutral-step (N.ne-case () motive branches) (ι-bounded-suc found arity)
    neutral-step (N.ne-case scrutinee motive branches) (ξ-case step) = a-case (neutral-step scrutinee step)
    neutral-step (N.ne-case scrutinee motive branches) (ξ-case-motive step) = a-motive (normal-step motive step)
    neutral-step (N.ne-case scrutinee motive branches) (ξ-case-brs steps) = a-branches (branches-path branches steps)
    terms-step : ∀ {args x′} → N.Normals sig args → (i : Fin (len args))
      → (step : _⇝_ sig (lookupAt args i) x′) → Step step
    terms-step (N.nf∷ head tail) zero step = normal-step head step
    terms-step (N.nf∷ head tail) (suc i) step = terms-step tail i step
    normal-path : ∀ {t u} → N.Normal sig t → (steps : _⇝*_ sig t u) → Path steps
    normal-path normal ⇝*-refl = a-refl
    normal-path normal (⇝*-step step tail) with step-identity (normal-step normal step)
    ... | refl = a-step (normal-step normal step) (normal-path normal tail)
    branches-path : ∀ {bs bs′} → N.Branches sig bs → (steps : _⇝*ᵇ_ sig bs bs′) → BranchPath steps
    branches-path N.nb[] ⇝ᵇ-nil = a[]
    branches-path (N.nb∷ head tail) (⇝ᵇ-cons body rest) = a∷ (normal-path head body) (branches-path tail rest)

  no-changing-step : ∀ {t u} → N.Normal sig t → _⇝_ sig t u → t ≢ u → ⊥
  no-changing-step normal step different = different (step-identity (normal-step normal step))
  path-invariant : ∀ {t u} → N.Normal sig t → _⇝*_ sig t u → t ≡ u
  path-invariant normal steps = path-identity (normal-path normal steps)

no-delta : Signature
no-delta = record { body = λ _ → nothing ; type-of = λ _ → nothing }
mutual
  strict-embedding : ∀ {t} → Q.BetaZetaNormal t → N.Normal no-delta t
  strict-embedding Q.normal-type = N.nf-type
  strict-embedding Q.normal-atom-type = N.nf-atom-type
  strict-embedding Q.normal-atom = N.nf-atom
  strict-embedding (Q.normal-pi domain body) = N.nf-pi (strict-embedding domain) (strict-embedding body)
  strict-embedding (Q.normal-lam domain body) = N.nf-lam (strict-embedding domain) (strict-embedding body)
  strict-embedding (Q.normal-ctor fields) = N.nf-ctor (strict-spine fields)
  strict-embedding (Q.normal-data params indices) = N.nf-data (strict-spine params) (strict-spine indices)
  strict-embedding (Q.normal-neutral head) = N.nf-neutral (strict-neutral head)
  strict-neutral : ∀ {t} → Q.NeutralNormal t → N.Residual no-delta t
  strict-neutral Q.normal-var = N.ne-var
  strict-neutral Q.normal-global = N.ne-global refl
  strict-neutral (Q.normal-app function argument) = N.ne-app (strict-neutral function) (strict-embedding argument)
  strict-spine : ∀ {ts} → Q.SpineNormal ts → N.Normals no-delta ts
  strict-spine Q.normal[] = N.nf[]
  strict-spine (Q.normal∷ head tail) = N.nf∷ (strict-embedding head) (strict-spine tail)
