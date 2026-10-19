------------------------------------------------------------------------
-- A bounded NON-VACUITY witness for the Conversion RECORD, not NbE.
--
-- Interpret lets by substitution; retain rigid type heads, variables,
-- applications, binders, effects and cases structurally. Deliberately
-- forget ALL constructors/literals into one opaque leaf, satisfying the
-- compact-literal equations without claiming faithful value equality.
--
-- This total zeta-only algebra does NOT validate full ReduceConv (in
-- particular beta), eta, or implementation refinement. Its purpose is
-- to inhabit EVERY record field and exercise non-rigid converted types.
-- Renaming/substitution laws use the existing funext assumption only.
------------------------------------------------------------------------
module Proof.ConversionModel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Core.Syntax
open import Core.TypeHeads
open import Core.Typing using (Conversion; All2; a2[]; a2∷)
open import Proof.Substitution using (rename-topSub; subst-topSub)

mutual
  interpret : Term → Term
  interpret (tm-type l) = tm-type l
  interpret (tm-var k) = tm-var k
  interpret (tm-pi g d c) = tm-pi g (interpret d) (interpret c)
  interpret (tm-lam g d b) = tm-lam g (interpret d) (interpret b)
  interpret (tm-let g ty v b) = substTopT (interpret v) (interpret b)
  interpret (tm-app f a) = tm-app (interpret f) (interpret a)
  interpret (tm-data n ps is) = tm-data n (interpretTerms ps) (interpretTerms is)
  interpret (tm-ctor n args) = tm-absurd
  interpret (tm-case s m brs) =
    tm-case (interpret s) (interpret m) (interpretBranches brs)
  interpret (tm-global n) = tm-global n
  interpret tm-int_type = tm-int_type
  interpret (tm-int_lit k) = tm-absurd
  interpret (tm-nat_lit k) = tm-absurd
  interpret (tm-bounded_lit k) = tm-absurd
  interpret tm-float_type = tm-float_type
  interpret tm-float_lit = tm-absurd
  interpret tm-binary_type = tm-binary_type
  interpret tm-atom_type = tm-atom_type
  interpret (tm-atom_lit n) = tm-absurd
  interpret (tm-effect_type a) = tm-effect_type (interpret a)
  interpret (tm-effect_pure a) = tm-effect_pure (interpret a)
  interpret (tm-effect_bind e k) = tm-effect_bind (interpret e) (interpret k)
  interpret (tm-hole n) = tm-hole n
  interpret tm-absurd = tm-absurd

  interpretTerms : List Term → List Term
  interpretTerms [] = []
  interpretTerms (x ∷ xs) = interpret x ∷ interpretTerms xs

  interpretBranch : Branch → Branch
  interpretBranch (cn , ar , b) = cn , ar , interpret b

  interpretBranches : List Branch → List Branch
  interpretBranches [] = []
  interpretBranches (x ∷ xs) = interpretBranch x ∷ interpretBranches xs

mutual
  interpret-rename : ∀ ρ t → interpret (rename ρ t) ≡ rename ρ (interpret t)
  interpret-rename ρ (tm-type l) = refl
  interpret-rename ρ (tm-var k) = refl
  interpret-rename ρ (tm-pi g d c) =
    cong₂ (tm-pi g) (interpret-rename ρ d) (interpret-rename (ext ρ) c)
  interpret-rename ρ (tm-lam g d b) =
    cong₂ (tm-lam g) (interpret-rename ρ d) (interpret-rename (ext ρ) b)
  interpret-rename ρ (tm-let g ty v b) =
    trans (cong₂ substTopT (interpret-rename ρ v) (interpret-rename (ext ρ) b))
          (sym (rename-topSub ρ (interpret v) (interpret b)))
  interpret-rename ρ (tm-app f a) =
    cong₂ tm-app (interpret-rename ρ f) (interpret-rename ρ a)
  interpret-rename ρ (tm-data n ps is) =
    cong₂ (tm-data n) (interpret-rename-terms ρ ps) (interpret-rename-terms ρ is)
  interpret-rename ρ (tm-ctor n args) = refl
  interpret-rename ρ (tm-case s m brs) =
    cong₃ tm-case (interpret-rename ρ s) (interpret-rename ρ m)
                 (interpret-rename-branches ρ brs)
  interpret-rename ρ (tm-global n) = refl
  interpret-rename ρ tm-int_type = refl
  interpret-rename ρ (tm-int_lit k) = refl
  interpret-rename ρ (tm-nat_lit k) = refl
  interpret-rename ρ (tm-bounded_lit k) = refl
  interpret-rename ρ tm-float_type = refl
  interpret-rename ρ tm-float_lit = refl
  interpret-rename ρ tm-binary_type = refl
  interpret-rename ρ tm-atom_type = refl
  interpret-rename ρ (tm-atom_lit n) = refl
  interpret-rename ρ (tm-effect_type a) = cong tm-effect_type (interpret-rename ρ a)
  interpret-rename ρ (tm-effect_pure a) = cong tm-effect_pure (interpret-rename ρ a)
  interpret-rename ρ (tm-effect_bind e k) =
    cong₂ tm-effect_bind (interpret-rename ρ e) (interpret-rename ρ k)
  interpret-rename ρ (tm-hole n) = refl
  interpret-rename ρ tm-absurd = refl

  interpret-rename-terms : ∀ ρ ts
    → interpretTerms (renameTerms ρ ts) ≡ renameTerms ρ (interpretTerms ts)
  interpret-rename-terms ρ [] = refl
  interpret-rename-terms ρ (x ∷ xs) =
    cong₂ _∷_ (interpret-rename ρ x) (interpret-rename-terms ρ xs)

  interpret-rename-branch : ∀ ρ br
    → interpretBranch (renameBranch ρ br) ≡ renameBranch ρ (interpretBranch br)
  interpret-rename-branch ρ (cn , ar , b) =
    cong (λ x → cn , ar , x) (interpret-rename (ext^ ar ρ) b)

  interpret-rename-branches : ∀ ρ brs
    → interpretBranches (renameBranches ρ brs) ≡ renameBranches ρ (interpretBranches brs)
  interpret-rename-branches ρ [] = refl
  interpret-rename-branches ρ (x ∷ xs) =
    cong₂ _∷_ (interpret-rename-branch ρ x) (interpret-rename-branches ρ xs)

interpretSub : Sub → Sub
interpretSub σ k = interpret (σ k)

interpret-ext : ∀ ar σ k
  → interpretSub (extSub^ ar σ) k ≡ extSub^ ar (interpretSub σ) k
interpret-ext zero σ k = refl
interpret-ext (suc ar) σ zero = refl
interpret-ext (suc ar) σ (suc k) =
  trans (interpret-rename wk (extSub^ ar σ k))
        (cong (rename wk) (interpret-ext ar σ k))

mutual
  interpret-subst : ∀ σ t → interpret (substS σ t) ≡ substS (interpretSub σ) (interpret t)
  interpret-subst σ (tm-type l) = refl
  interpret-subst σ (tm-var k) = refl
  interpret-subst σ (tm-pi g d c) =
    cong₂ (tm-pi g) (interpret-subst σ d) (interpret-subst-binders 1 σ c)
  interpret-subst σ (tm-lam g d b) =
    cong₂ (tm-lam g) (interpret-subst σ d) (interpret-subst-binders 1 σ b)
  interpret-subst σ (tm-let g ty v b) =
    trans (cong₂ substTopT (interpret-subst σ v) (interpret-subst-binders 1 σ b))
          (sym (subst-topSub (interpretSub σ) (interpret v) (interpret b)))
  interpret-subst σ (tm-app f a) =
    cong₂ tm-app (interpret-subst σ f) (interpret-subst σ a)
  interpret-subst σ (tm-data n ps is) =
    cong₂ (tm-data n) (interpret-subst-terms σ ps) (interpret-subst-terms σ is)
  interpret-subst σ (tm-ctor n args) = refl
  interpret-subst σ (tm-case s m brs) =
    cong₃ tm-case (interpret-subst σ s) (interpret-subst σ m)
                 (interpret-subst-branches σ brs)
  interpret-subst σ (tm-global n) = refl
  interpret-subst σ tm-int_type = refl
  interpret-subst σ (tm-int_lit k) = refl
  interpret-subst σ (tm-nat_lit k) = refl
  interpret-subst σ (tm-bounded_lit k) = refl
  interpret-subst σ tm-float_type = refl
  interpret-subst σ tm-float_lit = refl
  interpret-subst σ tm-binary_type = refl
  interpret-subst σ tm-atom_type = refl
  interpret-subst σ (tm-atom_lit n) = refl
  interpret-subst σ (tm-effect_type a) = cong tm-effect_type (interpret-subst σ a)
  interpret-subst σ (tm-effect_pure a) = cong tm-effect_pure (interpret-subst σ a)
  interpret-subst σ (tm-effect_bind e k) =
    cong₂ tm-effect_bind (interpret-subst σ e) (interpret-subst σ k)
  interpret-subst σ (tm-hole n) = refl
  interpret-subst σ tm-absurd = refl

  interpret-subst-binders : ∀ ar σ t
    → interpret (substS (extSub^ ar σ) t) ≡ substS (extSub^ ar (interpretSub σ)) (interpret t)
  interpret-subst-binders ar σ t =
    trans (interpret-subst (extSub^ ar σ) t)
          (cong (λ τ → substS τ (interpret t)) (funext (interpret-ext ar σ)))

  interpret-subst-terms : ∀ σ ts
    → interpretTerms (substTermsS σ ts) ≡ substTermsS (interpretSub σ) (interpretTerms ts)
  interpret-subst-terms σ [] = refl
  interpret-subst-terms σ (x ∷ xs) =
    cong₂ _∷_ (interpret-subst σ x) (interpret-subst-terms σ xs)

  interpret-subst-branch : ∀ σ br
    → interpretBranch (substBranchS σ br) ≡ substBranchS (interpretSub σ) (interpretBranch br)
  interpret-subst-branch σ (cn , ar , b) =
    cong (λ x → cn , ar , x) (interpret-subst-binders ar σ b)

  interpret-subst-branches : ∀ σ brs
    → interpretBranches (substBranchesS σ brs) ≡ substBranchesS (interpretSub σ) (interpretBranches brs)
  interpret-subst-branches σ [] = refl
  interpret-subst-branches σ (x ∷ xs) =
    cong₂ _∷_ (interpret-subst-branch σ x) (interpret-subst-branches σ xs)

infix 4 _≃_
_≃_ : Term → Term → Set
t ≃ u = interpret t ≡ interpret u

model-rename : ∀ {t u} ρ → t ≃ u → rename ρ t ≃ rename ρ u
model-rename {t} {u} ρ eq =
  trans (interpret-rename ρ t)
        (trans (cong (rename ρ) eq) (sym (interpret-rename ρ u)))

model-subst : ∀ {t u} σ → t ≃ u → substS σ t ≃ substS σ u
model-subst {t} {u} σ eq =
  trans (interpret-subst σ t)
        (trans (cong (substS (interpretSub σ)) eq) (sym (interpret-subst σ u)))

model-subst-cong : ∀ {t σ σ′} → (∀ k → σ k ≃ σ′ k) → substS σ t ≃ substS σ′ t
model-subst-cong {t} {σ} {σ′} eq =
  trans (interpret-subst σ t)
        (trans (cong (λ τ → substS τ (interpret t)) (funext eq))
               (sym (interpret-subst σ′ t)))

interpret-head : ∀ {t h} → HasTypeHead t h → HasTypeHead (interpret t) h
interpret-head ty-universe = ty-universe
interpret-head ty-pi = ty-pi
interpret-head ty-data = ty-data
interpret-head ty-int = ty-int
interpret-head ty-float = ty-float
interpret-head ty-binary = ty-binary
interpret-head ty-atom = ty-atom
interpret-head ty-effect = ty-effect

model-heads : ∀ {t u h h′}
  → HasTypeHead t h → HasTypeHead u h′ → t ≃ u → h ≡ h′
model-heads {h = h} ht hu eq =
  type-head-unique (subst (λ v → HasTypeHead v h) eq (interpret-head ht)) (interpret-head hu)

pi-parts : ∀ {g d c g′ d′ c′}
  → tm-pi g′ d′ c′ ≡ tm-pi g d c → g′ ≡ g × d′ ≡ d × c′ ≡ c
pi-parts refl = refl , refl , refl

model-spine : ∀ {ts us} → All2 _≃_ ts us → interpretTerms ts ≡ interpretTerms us
model-spine a2[] = refl
model-spine (a2∷ eq rest) = cong₂ _∷_ eq (model-spine rest)

model : Conversion
model = record
  { _≈_ = _≃_
  ; ≈-refl = refl
  ; ≈-sym = sym
  ; ≈-trans = trans
  ; ≈-pi = cong₂ (tm-pi _)
  ; ≈-app = cong₂ tm-app
  ; ≈-data = λ ps is → cong₂ (tm-data _) (model-spine ps) (model-spine is)
  ; ≈-ctor = λ _ → refl
  ; ≈-effect_type = cong tm-effect_type
  ; ≈-effect_pure = cong tm-effect_pure
  ; ≈-effect_bind = cong₂ tm-effect_bind
  ; ≈-rename = λ {t} {u} → model-rename {t} {u}
  ; ≈-subst = λ {t} {u} → model-subst {t} {u}
  ; ≈-subst-cong = λ {t} {σ} {σ′} → model-subst-cong {t} {σ} {σ′}
  ; ≈-heads = model-heads
  ; ≈-pi-components = λ eq → pi-parts eq
  ; ≈-nat-zero = refl
  ; ≈-nat-suc = refl
  ; ≈-bounded-zero = refl
  ; ≈-bounded-suc = refl
  }

interpret-topSub : ∀ v k → interpretSub (topSub v) k ≡ topSub (interpret v) k
interpret-topSub v zero = refl
interpret-topSub v (suc k) = refl

-- All zeta equations, not merely one closed example, hold in this model.
model-zeta : ∀ g ty v b → tm-let g ty v b ≃ substTopT v b
model-zeta g ty v b =
  sym (trans (interpret-subst (topSub v) b)
             (cong (λ σ → substS σ (interpret b)) (funext (interpret-topSub v))))
