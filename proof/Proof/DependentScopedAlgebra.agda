------------------------------------------------------------------------
-- Exact, scope-aware algebra for GENERAL native case transport.
-- Agreement is needed only on declaration-local slots. No typing or
-- preservation assumptions, and no closed dependent-entry premise.
------------------------------------------------------------------------
module Proof.DependentScopedAlgebra where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (+-suc; +-comm)
open import Data.List using (List; []; _∷_; _++_; length; map; reverse)
open import Data.List.Properties using (length-reverse)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Core.Syntax
open import Core.Signature
open import Core.Grade using (unrestricted)
open import Core.Universe using (Level)
open import Core.Typing using (surface-field-vars)
open import Core.Verification using (ScopedTele; tele[]; tele∷)
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentNaturality as Earlier
open import Proof.Substitution
  using (rename-subst; subst-compose; renameSub; substCompose;
         renameSub-extSub-eq; extSub-compose; rename-raise;
         subst-extSub^-shift; rename-surface-fields; subst-surface-fields)

Agree : ℕ → Sub → Sub → Set
Agree d σ τ = ∀ k → k < d → σ k ≡ τ k

extend-agree : ∀ {d σ τ} → Agree d σ τ → Agree (suc d) (extSub σ) (extSub τ)
extend-agree equal zero bound = refl
extend-agree equal (suc k) (s≤s bound) = cong (rename wk) (equal k bound)

extendⁿ-agree : ∀ ar {d σ τ} → Agree d σ τ
  → Agree (d + ar) (extSub^ ar σ) (extSub^ ar τ)
extendⁿ-agree zero {d} {σ} {τ} equal =
  subst (λ n → Agree n σ τ) (sym (Data.Nat.Properties.+-identityʳ d)) equal
extendⁿ-agree (suc ar) {d} {σ} {τ} equal =
  subst (λ n → Agree n (extSub^ (suc ar) σ) (extSub^ (suc ar) τ))
    (sym (+-suc d ar)) (extend-agree (extendⁿ-agree ar equal))

mutual
  subst-agree : ∀ {d σ τ t} → Scoped d t → Agree d σ τ → substS σ t ≡ substS τ t
  subst-agree sc-type equal = refl
  subst-agree (sc-var bound) equal = equal _ bound
  subst-agree (sc-pi d c) equal =
    cong₂ (tm-pi _) (subst-agree d equal) (subst-agree c (extend-agree equal))
  subst-agree (sc-lam d b) equal =
    cong₂ (tm-lam _) (subst-agree d equal) (subst-agree b (extend-agree equal))
  subst-agree (sc-let ty v b) equal = cong₃ (tm-let _)
    (subst-agree ty equal) (subst-agree v equal) (subst-agree b (extend-agree equal))
  subst-agree (sc-app f a) equal = cong₂ tm-app (subst-agree f equal) (subst-agree a equal)
  subst-agree (sc-data ps is) equal =
    cong₂ (tm-data _) (terms-agree ps equal) (terms-agree is equal)
  subst-agree (sc-ctor args) equal = cong (tm-ctor _) (terms-agree args equal)
  subst-agree (sc-case s m brs) equal = cong₃ tm-case
    (subst-agree s equal) (subst-agree m equal) (branches-agree brs equal)
  subst-agree sc-global equal = refl
  subst-agree sc-int_type equal = refl
  subst-agree sc-int_lit equal = refl
  subst-agree sc-nat_lit equal = refl
  subst-agree sc-bounded_lit equal = refl
  subst-agree sc-float_type equal = refl
  subst-agree sc-float_lit equal = refl
  subst-agree sc-binary_type equal = refl
  subst-agree sc-atom_type equal = refl
  subst-agree sc-atom_lit equal = refl
  subst-agree (sc-effect_type t) equal = cong tm-effect_type (subst-agree t equal)
  subst-agree (sc-effect_pure t) equal = cong tm-effect_pure (subst-agree t equal)
  subst-agree (sc-effect_bind e k) equal = cong₂ tm-effect_bind (subst-agree e equal) (subst-agree k equal)
  subst-agree sc-hole equal = refl
  subst-agree sc-absurd equal = refl

  terms-agree : ∀ {d σ τ ts} → ScopedTerms d ts → Agree d σ τ
    → substTermsS σ ts ≡ substTermsS τ ts
  terms-agree st[] equal = refl
  terms-agree (st∷ scoped rest) equal =
    cong₂ _∷_ (subst-agree scoped equal) (terms-agree rest equal)

  branches-agree : ∀ {d σ τ brs} → ScopedBranches d brs → Agree d σ τ
    → substBranchesS σ brs ≡ substBranchesS τ brs
  branches-agree sb[] equal = refl
  branches-agree (sb∷ (sbranch {cn = name} {ar = ar} body) rest) equal =
    cong₂ _∷_ (cong (λ b → name , ar , b) (subst-agree body (extendⁿ-agree ar equal)))
      (branches-agree rest equal)

prefix-tail : ∀ xs σ τ → Agree (length xs) (F.prefix xs σ) (F.prefix xs τ)
prefix-tail [] σ τ k ()
prefix-tail (x ∷ xs) σ τ zero bound = refl
prefix-tail (x ∷ xs) σ τ (suc k) (s≤s bound) = prefix-tail xs σ τ k bound

advance-tail : ∀ xs σ τ → Agree (length xs) (F.advance xs σ) (F.advance xs τ)
advance-tail xs σ τ k bound =
  trans (F.advance-reverse xs σ k)
    (trans (prefix-tail (reverse xs) σ τ k
      (subst (λ n → k < n) (sym (length-reverse xs)) bound))
      (sym (F.advance-reverse xs τ k)))

advance-map : ∀ (f : Term → Term) xs σ i
  → f (F.advance xs σ i) ≡ F.advance (map f xs) (λ k → f (σ k)) i
advance-map f [] σ i = refl
advance-map f (x ∷ xs) σ i =
  trans (advance-map f xs (F.push x σ) i)
    (cong (λ τ → F.advance (map f xs) τ i)
      (funext (λ { zero → refl ; (suc k) → refl })))

map-length : ∀ (f : Term → Term) xs → length (map f xs) ≡ length xs
map-length f [] = refl
map-length f (x ∷ xs) = cong suc (map-length f xs)

frame-map-agrees : ∀ f ps
  → Agree (length ps) (λ i → f (F.advance ps F.identity i))
      (F.advance (map f ps) F.identity)
frame-map-agrees f ps k bound =
  trans (advance-map f ps F.identity k)
    (advance-tail (map f ps) (λ i → f (F.identity i)) F.identity k
      (subst (λ n → k < n) (sym (map-length f ps)) bound))

rename-frame-agrees : ∀ ρ ps → Agree (length ps)
  (renameSub ρ (F.advance ps F.identity)) (F.advance (renameTerms ρ ps) F.identity)
rename-frame-agrees ρ ps k bound =
  trans (frame-map-agrees (rename ρ) ps k bound)
    (cong (λ xs → F.advance xs F.identity k) (sym (renameTerms-map ρ ps)))
subst-frame-agrees : ∀ σ ps → Agree (length ps)
  (substCompose σ (F.advance ps F.identity)) (F.advance (substTermsS σ ps) F.identity)
subst-frame-agrees σ ps k bound =
  trans (frame-map-agrees (substS σ) ps k bound)
    (cong (λ xs → F.advance xs F.identity k) (sym (substTerms-map σ ps)))

piTele-agree : ∀ {d σ τ tele} → ScopedTele d tele → Agree d σ τ → ∀ body
  → Native.piTele σ tele body ≡ Native.piTele τ tele body
piTele-agree tele[] equal body = refl
piTele-agree (tele∷ scoped rest) equal body =
  cong₂ (tm-pi unrestricted) (subst-agree scoped equal) (piTele-agree rest (extend-agree equal) body)

opened-agree : ∀ {n m d} {Γ : Core.Typing.Ctx n} {Ω : Core.Typing.Ctx m} {σ τ tele}
  → ScopedTele d tele → Agree d σ τ → Native.Opened Γ σ tele Ω → Native.Opened Γ τ tele Ω
opened-agree tele[] equal Native.op[] = Native.op[]
opened-agree {Γ = Γ} {Ω = Ω} {σ = σ} {τ = τ}
  (tele∷ {ty = T} {rest = tele} scoped scopes) equal (Native.op∷ rest) =
  Native.op∷ (subst (λ Δ → Native.Opened Δ (extSub τ) tele Ω)
    (cong (Core.Typing.extend Γ) (subst-agree scoped equal))
    (opened-agree scopes (extend-agree equal) rest))

rename-piTele : ∀ ρ ps tele body → ScopedTele (length ps) tele
  → rename ρ (Native.piTele (F.advance ps F.identity) tele body)
    ≡ Native.piTele (F.advance (renameTerms ρ ps) F.identity) tele
      (rename (ext^ (length tele) ρ) body)
rename-piTele ρ ps tele body scoped =
  trans (Earlier.rename-piTele ρ (F.advance ps F.identity) tele body)
    (piTele-agree scoped (rename-frame-agrees ρ ps) _)

subst-piTele : ∀ σ ps tele body → ScopedTele (length ps) tele
  → substS σ (Native.piTele (F.advance ps F.identity) tele body)
    ≡ Native.piTele (F.advance (substTermsS σ ps) F.identity) tele
      (substS (extSub^ (length tele) σ) body)
subst-piTele σ ps tele body scoped =
  trans (Earlier.subst-piTele σ (F.advance ps F.identity) tele body)
    (piTele-agree scoped (subst-frame-agrees σ ps) _)

rename-shifted : ∀ ar ρ ps
  → renameTerms (ext^ ar ρ) (map (shift ar 0) ps) ≡ map (shift ar 0) (renameTerms ρ ps)
rename-shifted ar ρ [] = refl
rename-shifted ar ρ (p ∷ ps) =
  cong₂ _∷_ (sym (rename-raise ar ρ p)) (rename-shifted ar ρ ps)
subst-shifted : ∀ ar σ ps
  → substTermsS (extSub^ ar σ) (map (shift ar 0) ps) ≡ map (shift ar 0) (substTermsS σ ps)
subst-shifted ar σ [] = refl
subst-shifted ar σ (p ∷ ps) =
  cong₂ _∷_ (subst-extSub^-shift ar σ p) (subst-shifted ar σ ps)

rename-motiveType : ∀ ρ family ps level
  → ScopedTele (length ps) (fam-indices family)
  → rename ρ (Native.motiveType family ps level)
    ≡ Native.motiveType family (renameTerms ρ ps) level
rename-motiveType ρ family ps level scoped =
  trans (rename-piTele ρ ps (fam-indices family) _ scoped)
    (cong (Native.piTele (F.advance (renameTerms ρ ps) F.identity) (fam-indices family))
      (cong (λ d → tm-pi unrestricted d (tm-type level))
        (cong₂ (tm-data (fam-name family)) (rename-shifted ar ρ ps) (rename-surface-fields ar ρ))))
  where ar = length (fam-indices family)

renameSub-extended : ∀ ar ρ σ
  → renameSub (ext^ ar ρ) (extSub^ ar σ) ≡ extSub^ ar (renameSub ρ σ)
renameSub-extended zero ρ σ = refl
renameSub-extended (suc ar) ρ σ =
  trans (renameSub-extSub-eq (ext^ ar ρ) (extSub^ ar σ))
    (cong extSub (renameSub-extended ar ρ σ))

compose-extended : ∀ ar σ τ
  → substCompose (extSub^ ar σ) (extSub^ ar τ) ≡ extSub^ ar (substCompose σ τ)
compose-extended zero σ τ = refl
compose-extended (suc ar) σ τ =
  trans (funext (extSub-compose (extSub^ ar σ) (extSub^ ar τ)))
    (cong extSub (compose-extended ar σ τ))

rename-specialize : ∀ ar ρ ps t → Scoped (length ps + ar) t
  → rename (ext^ ar ρ) (F.specializeParameters ar ps t)
    ≡ F.specializeParameters ar (renameTerms ρ ps) t
rename-specialize ar ρ ps t scoped =
  trans (rename-subst (ext^ ar ρ) (extSub^ ar (F.advance ps F.identity)) t)
    (trans (cong (λ σ → substS σ t) (renameSub-extended ar ρ (F.advance ps F.identity)))
      (subst-agree scoped (extendⁿ-agree ar (rename-frame-agrees ρ ps))))

subst-specialize : ∀ ar σ ps t → Scoped (length ps + ar) t
  → substS (extSub^ ar σ) (F.specializeParameters ar ps t)
    ≡ F.specializeParameters ar (substTermsS σ ps) t
subst-specialize ar σ ps t scoped =
  trans (subst-compose (extSub^ ar σ) (extSub^ ar (F.advance ps F.identity)) t)
    (trans (cong (λ τ → substS τ t) (compose-extended ar σ (F.advance ps F.identity)))
      (subst-agree scoped (extendⁿ-agree ar (subst-frame-agrees σ ps))))

rename-specialized : ∀ ar ρ ps ts → ScopedTerms (length ps + ar) ts
  → renameTerms (ext^ ar ρ) (map (F.specializeParameters ar ps) ts)
    ≡ map (F.specializeParameters ar (renameTerms ρ ps)) ts
rename-specialized ar ρ ps [] st[] = refl
rename-specialized ar ρ ps (t ∷ ts) (st∷ scoped scopes) =
  cong₂ _∷_ (rename-specialize ar ρ ps t scoped) (rename-specialized ar ρ ps ts scopes)
subst-specialized : ∀ ar σ ps ts → ScopedTerms (length ps + ar) ts
  → substTermsS (extSub^ ar σ) (map (F.specializeParameters ar ps) ts)
    ≡ map (F.specializeParameters ar (substTermsS σ ps)) ts
subst-specialized ar σ ps [] st[] = refl
subst-specialized ar σ ps (t ∷ ts) (st∷ scoped scopes) =
  cong₂ _∷_ (subst-specialize ar σ ps t scoped) (subst-specialized ar σ ps ts scopes)

rename-apps : ∀ ρ f args
  → rename ρ (Native.apps f args) ≡ Native.apps (rename ρ f) (renameTerms ρ args)
rename-apps ρ f [] = refl
rename-apps ρ f (a ∷ args) = rename-apps ρ (tm-app f a) args
subst-apps : ∀ σ f args
  → substS σ (Native.apps f args) ≡ Native.apps (substS σ f) (substTermsS σ args)
subst-apps σ f [] = refl
subst-apps σ f (a ∷ args) = subst-apps σ (tm-app f a) args

rename-case-goal : ∀ ρ mot is s
  → rename ρ (Native.apps mot (is ++ s ∷ []))
    ≡ Native.apps (rename ρ mot) (renameTerms ρ is ++ rename ρ s ∷ [])
rename-case-goal ρ mot is s =
  trans (rename-apps ρ mot (is ++ s ∷ []))
    (cong (Native.apps (rename ρ mot)) (Earlier.rename-append ρ is (s ∷ [])))
subst-case-goal : ∀ σ mot is s
  → substS σ (Native.apps mot (is ++ s ∷ []))
    ≡ Native.apps (substS σ mot) (substTermsS σ is ++ substS σ s ∷ [])
subst-case-goal σ mot is s =
  trans (subst-apps σ mot (is ++ s ∷ []))
    (cong (Native.apps (substS σ mot)) (Earlier.subst-append σ is (s ∷ [])))

rename-branchGoal : ∀ ρ name ps ctor mot
  → ScopedTerms (length ps + length (ctor-args ctor)) (ctor-indices ctor)
  → rename (ext^ (length (ctor-args ctor)) ρ) (Native.branchGoal name ps ctor mot)
    ≡ Native.branchGoal name (renameTerms ρ ps) ctor (rename ρ mot)
rename-branchGoal ρ name ps ctor mot scoped =
  trans (rename-apps (ext^ ar ρ) (shift ar 0 mot)
    (map (F.specializeParameters ar ps) (ctor-indices ctor)
      ++ tm-ctor name (surface-field-vars ar) ∷ []))
    (cong₂ Native.apps (sym (rename-raise ar ρ mot))
      (trans (Earlier.rename-append (ext^ ar ρ)
        (map (F.specializeParameters ar ps) (ctor-indices ctor))
        (tm-ctor name (surface-field-vars ar) ∷ []))
        (cong₂ _++_ (rename-specialized ar ρ ps (ctor-indices ctor) scoped)
          (cong (λ args → tm-ctor name args ∷ []) (rename-surface-fields ar ρ)))))
  where ar = length (ctor-args ctor)

subst-branchGoal : ∀ σ name ps ctor mot
  → ScopedTerms (length ps + length (ctor-args ctor)) (ctor-indices ctor)
  → substS (extSub^ (length (ctor-args ctor)) σ) (Native.branchGoal name ps ctor mot)
    ≡ Native.branchGoal name (substTermsS σ ps) ctor (substS σ mot)
subst-branchGoal σ name ps ctor mot scoped =
  trans (subst-apps (extSub^ ar σ) (shift ar 0 mot)
    (map (F.specializeParameters ar ps) (ctor-indices ctor)
      ++ tm-ctor name (surface-field-vars ar) ∷ []))
    (cong₂ Native.apps (subst-extSub^-shift ar σ mot)
      (trans (Earlier.subst-append (extSub^ ar σ)
        (map (F.specializeParameters ar ps) (ctor-indices ctor))
        (tm-ctor name (surface-field-vars ar) ∷ []))
        (cong₂ _++_ (subst-specialized ar σ ps (ctor-indices ctor) scoped)
          (cong (λ args → tm-ctor name args ∷ []) (subst-surface-fields ar σ)))))
  where ar = length (ctor-args ctor)

subst-motiveType : ∀ σ family ps level
  → ScopedTele (length ps) (fam-indices family)
  → substS σ (Native.motiveType family ps level)
    ≡ Native.motiveType family (substTermsS σ ps) level
subst-motiveType σ family ps level scoped =
  trans (subst-piTele σ ps (fam-indices family) _ scoped)
    (cong (Native.piTele (F.advance (substTermsS σ ps) F.identity) (fam-indices family))
      (cong (λ d → tm-pi unrestricted d (tm-type level))
        (cong₂ (tm-data (fam-name family)) (subst-shifted ar σ ps) (subst-surface-fields ar σ))))
  where ar = length (fam-indices family)
