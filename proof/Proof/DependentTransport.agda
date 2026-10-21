------------------------------------------------------------------------
-- Actual native typing transport for the CASE-FREE derivation fragment.
-- Support includes hidden parameter witnesses, not just runtime syntax.
-- No base typing, closed-registry premise, or preservation oracle.
-- Whole-case/context/motive transport remains a separate obligation.
------------------------------------------------------------------------
module Proof.DependentTransport where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.List.Properties using (length-reverse)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; ⟨⟩; extend; lookup; lookup-extend; Conversion)
open import Core.Verification using (ScopedTele; tele[]; tele∷)
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentCoherence as Frames
open import Proof.LocalFrame using (rename-local; subst-local)
open import Proof.Progress using (Final; FinalTerms; ft[]; ft∷)
open import Proof.Substitution
  using (rename-topSub; subst-topSub; rename-closed; substS-closed;
         renameTerms-reverse; substTerms-reverse; subst-extSub-wk)
open import Proof.Substitution using (substS-idSub)
open import Proof.LocalFrame using (push-undoes-wk)

module Transport (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv
  module C = Frames.NativeFrames ind sig conv
  open C using (Renaming; index; agrees; types; extend-renaming)
  open Conversion conv

  -- These predicates inspect EXISTING native derivations. In particular,
  -- a constructor's invisible parameter spine is not omitted.
  mutual
    Supported⇒ : ∀ {n} {Γ : Ctx n} {t T} → Γ ⊢ t ⇒ T → Set
    Supported⇒ (⇒-pi d c) = Supported⇒ d × Supported⇒ c
    Supported⇒ (⇒-lam d b) = Supported⇒ d × Supported⇐ b
    Supported⇒ (⇒-app f a) = Supported⇒ f × Supported⇒ a
    Supported⇒ (⇒-let ty v b) = Supported⇒ ty × Supported⇐ v × Supported⇒ b
    Supported⇒ (⇒-data found ps is) = SupportedSpine ps × SupportedSpine is
    Supported⇒ (⇒-ctor found ps args) = SupportedSpine ps × SupportedSpine args
    Supported⇒ (⇒-case wf found s ps is mot branches covered) = ⊥
    Supported⇒ (⇒-effect_type t) = Supported⇒ t
    Supported⇒ (⇒-effect_pure t) = Supported⇒ t
    Supported⇒ (⇒-effect_bind e k) = Supported⇒ e × Supported⇒ k
    Supported⇒ (⇒-conv t equal) = Supported⇒ t
    Supported⇒ (⇒-cumul t le) = Supported⇒ t
    Supported⇒ _ = ⊤

    Supported⇐ : ∀ {n} {Γ : Ctx n} {t T} → Γ ⊢ t ⇐ T → Set
    Supported⇐ (⇐-lam d b) = Supported⇒ d × Supported⇐ b
    Supported⇐ ⇐-hole = ⊤
    Supported⇐ (⇐-infer t equal) = Supported⇒ t
    Supported⇐ (⇐-conv t equal) = Supported⇐ t
    Supported⇐ (⇐-cumul t le) = Supported⇒ t

    SupportedSpine : ∀ {n} {Γ : Ctx n} {locals args tele}
      → Spine Γ locals args tele → Set
    SupportedSpine sp[] = ⊤
    SupportedSpine (sp∷ arg rest) = Supported⇐ arg × SupportedSpine rest

  Infer : ∀ {n} → Ctx n → Term → Term → Set
  Infer Γ t T = Σ (Γ ⊢ t ⇒ T) Supported⇒
  Check : ∀ {n} → Ctx n → Term → Term → Set
  Check Γ t T = Σ (Γ ⊢ t ⇐ T) Supported⇐
  Arguments : ∀ {n} → Ctx n → List Term → List Term → Telescope → Set
  Arguments Γ locals args tele = Σ (Spine Γ locals args tele) SupportedSpine

  cast⇒ : ∀ {n} {Γ : Ctx n} {t t′ T T′}
    → t ≡ t′ → T ≡ T′ → Infer Γ t T → Infer Γ t′ T′
  cast⇒ refl refl evidence = evidence
  cast⇐ : ∀ {n} {Γ : Ctx n} {t t′ T T′}
    → t ≡ t′ → T ≡ T′ → Check Γ t T → Check Γ t′ T′
  cast⇐ refl refl evidence = evidence

  cast-arguments : ∀ {n} {Γ : Ctx n} {locals locals′ args tele}
    → locals ≡ locals′ → Arguments Γ locals args tele → Arguments Γ locals′ args tele
  cast-arguments refl evidence = evidence

  ren-length : ∀ ρ xs → length (renameTerms ρ xs) ≡ length xs
  ren-length ρ [] = refl
  ren-length ρ (x ∷ xs) = cong suc (ren-length ρ xs)
  sub-length : ∀ σ xs → length (substTermsS σ xs) ≡ length xs
  sub-length σ [] = refl
  sub-length σ (x ∷ xs) = cong suc (sub-length σ xs)

  -- All scope evidence comes from native declaration validity at actual
  -- lookup entries, never from individually closed dependent entries.
  parameter-scope : ∀ {name family}
    → SignatureValid → findFamily name (IndEnv.families ind) ≡ just family
    → ScopedTele 0 (fam-params family)
  parameter-scope valid found =
    C.declared-scoping (FamilyDeclaration.parameters (SignatureValid.family-declared valid found))
  declaration-size : ∀ {p} {Π : Ctx p} {tele} → Declared ⟨⟩ tele Π → length tele ≡ p
  declaration-size {tele = tele} pd =
    trans (sym (+-identityʳ (length tele))) (C.declared-length pd)

  index-scope : ∀ {n} {Γ : Ctx n} {name family ps}
    → SignatureValid → findFamily name (IndEnv.families ind) ≡ just family
    → Spine Γ [] ps (fam-params family)
    → ScopedTele (length (reverse ps)) (fam-indices family)
  index-scope {ps = ps} valid found params =
    subst (λ d → ScopedTele d _) (sym size)
      (C.declared-scoping (FamilyDeclaration.indices declaration))
    where
      declaration = SignatureValid.family-declared valid found
      size = trans (length-reverse ps)
        (trans (spine-length params) (declaration-size (FamilyDeclaration.parameters declaration)))

  field-scope : ∀ {n} {Γ : Ctx n} {name family ctor ps}
    → SignatureValid → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
    → Spine Γ [] ps (fam-params family)
    → ScopedTele (length (reverse ps)) (ctor-args ctor)
  field-scope {ps = ps} valid found params =
    subst (λ d → ScopedTele d _) (sym size)
      (C.declared-scoping (ConstructorDeclaration.fields declaration))
    where
      declaration = SignatureValid.constructor-declared valid found
      size = trans (length-reverse ps)
        (trans (spine-length params) (declaration-size (ConstructorDeclaration.parameters declaration)))

  module Valid (valid : SignatureValid) where
    mutual
      rename⇒ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ t T}
        → Renaming Γ Δ ρ → (der : Γ ⊢ t ⇒ T) → Supported⇒ der
        → Infer Δ (rename ρ t) (rename ρ T)
      rename⇒ ren (⇒-type level) good = ⇒-type level , tt
      rename⇒ {ρ = ρ} ren (⇒-var i) good =
        cast⇒ (cong tm-var (agrees ren i)) (types ren i) (⇒-var (index ren i) , tt)
      rename⇒ ren (⇒-pi d c) (gd , gc)
        with rename⇒ ren d gd | rename⇒ (extend-renaming ren _) c gc
      ... | d′ , gd′ | c′ , gc′ = ⇒-pi d′ c′ , gd′ , gc′
      rename⇒ ren (⇒-lam d b) (gd , gb)
        with rename⇒ ren d gd | rename⇐ (extend-renaming ren _) b gb
      ... | d′ , gd′ | b′ , gb′ = ⇒-lam d′ b′ , gd′ , gb′
      rename⇒ {ρ = ρ} ren (⇒-app {a = a} {c = c} f a-typed) (gf , ga)
        with rename⇒ ren f gf | rename⇒ ren a-typed ga
      ... | f′ , gf′ | a′ , ga′ =
        cast⇒ refl (sym (rename-topSub ρ a c)) (⇒-app f′ a′ , gf′ , ga′)
      rename⇒ {ρ = ρ} ren (⇒-let {v = v} {T = T} ty val body) (gt , gv , gb)
        with rename⇒ ren ty gt | rename⇐ ren val gv | rename⇒ (extend-renaming ren _) body gb
      ... | ty′ , gt′ | val′ , gv′ | body′ , gb′ =
        cast⇒ refl (sym (rename-topSub ρ v T)) (⇒-let ty′ val′ body′ , gt′ , gv′ , gb′)
      rename⇒ {ρ = ρ} ren (⇒-global found) good =
        cast⇒ refl (sym (rename-closed (proj₁ (SignatureValid.global-type valid found))))
          (⇒-global found , tt)
      rename⇒ ren ⇒-int_type good = ⇒-int_type , tt
      rename⇒ ren ⇒-float_type good = ⇒-float_type , tt
      rename⇒ ren ⇒-binary_type good = ⇒-binary_type , tt
      rename⇒ ren ⇒-atom_type good = ⇒-atom_type , tt
      rename⇒ ren ⇒-int_lit good = ⇒-int_lit , tt
      rename⇒ ren ⇒-float_lit good = ⇒-float_lit , tt
      rename⇒ ren ⇒-atom_lit good = ⇒-atom_lit , tt
      rename⇒ ren (⇒-nat_lit builtin found ps is) good = ⇒-nat_lit builtin found ps is , tt
      rename⇒ ren (⇒-bounded_lit builtin found ps is) good = ⇒-bounded_lit builtin found ps is , tt
      rename⇒ {Δ = Δ} {ρ = ρ} ren (⇒-data {ps = ps} found params indices) (gp , gi)
        with rename-spine ren (parameter-scope valid found) params gp
           | rename-spine ren (index-scope valid found params) indices gi
      ... | params′ , gp′ | indices′ , gi′
        with cast-arguments (renameTerms-reverse ρ ps) (indices′ , gi′)
      ... | i , gi = ⇒-data found params′ i , gp′ , gi
      rename⇒ {Δ = Δ} {ρ = ρ} ren
        (⇒-ctor {ps = ps} {args = args} {ctor = ctor} found params fields) (gp , gf)
        with rename-spine ren (parameter-scope valid (SignatureValid.owner-visible valid found)) params gp
           | rename-spine ren (field-scope valid found params) fields gf
      ... | params′ , gp′ | fields′ , gf′
        with cast-arguments (renameTerms-reverse ρ ps) (fields′ , gf′)
      ... | f , gf =
        cast⇒ refl (sym (cong (tm-data _ (renameTerms ρ ps))
          (C.registered-results-rename valid found params fields ρ)))
          (⇒-ctor found params′ f , gp′ , gf)
      rename⇒ ren (⇒-case wf found s ps is mot branches covered) ()
      rename⇒ ren (⇒-effect_type t) good with rename⇒ ren t good
      ... | t′ , good′ = ⇒-effect_type t′ , good′
      rename⇒ ren (⇒-effect_pure t) good with rename⇒ ren t good
      ... | t′ , good′ = ⇒-effect_pure t′ , good′
      rename⇒ {ρ = ρ} ren (⇒-effect_bind {B = B} e k) (ge , gk)
        with rename⇒ ren e ge | rename⇒ ren k gk
      ... | e′ , ge′ | k′ , gk′ =
        ⇒-effect_bind e′
          (proj₁ (cast⇒ refl (cong (λ T → tm-pi _ _ (tm-effect_type T))
            (sym (ext-wk-rename ρ B))) (k′ , gk′))) ,
        ge′ , proj₂ (cast⇒ refl (cong (λ T → tm-pi _ _ (tm-effect_type T))
          (sym (ext-wk-rename ρ B))) (k′ , gk′))
      rename⇒ {ρ = ρ} ren (⇒-conv t equal) good with rename⇒ ren t good
      ... | t′ , good′ = ⇒-conv t′ (≈-rename _ equal) , good′
      rename⇒ ren (⇒-cumul t le) good with rename⇒ ren t good
      ... | t′ , good′ = ⇒-cumul t′ le , good′

      rename⇐ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ t T}
        → Renaming Γ Δ ρ → (der : Γ ⊢ t ⇐ T) → Supported⇐ der
        → Check Δ (rename ρ t) (rename ρ T)
      rename⇐ ren (⇐-lam d b) (gd , gb)
        with rename⇒ ren d gd | rename⇐ (extend-renaming ren _) b gb
      ... | d′ , gd′ | b′ , gb′ = ⇐-lam d′ b′ , gd′ , gb′
      rename⇐ ren ⇐-hole good = ⇐-hole , tt
      rename⇐ ren (⇐-infer t equal) good with rename⇒ ren t good
      ... | t′ , good′ = ⇐-infer t′ (≈-rename _ equal) , good′
      rename⇐ ren (⇐-conv t equal) good with rename⇐ ren t good
      ... | t′ , good′ = ⇐-conv t′ (≈-rename _ equal) , good′
      rename⇐ ren (⇐-cumul t le) good with rename⇒ ren t good
      ... | t′ , good′ = ⇐-cumul t′ le , good′

      rename-spine : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ locals args tele}
        → Renaming Γ Δ ρ → ScopedTele (length locals) tele
        → (der : Spine Γ locals args tele) → SupportedSpine der
        → Arguments Δ (renameTerms ρ locals) (renameTerms ρ args) tele
      rename-spine ren tele[] sp[] good = sp[] , tt
      rename-spine {ρ = ρ} {locals = locals} ren
        (tele∷ {ty = T} scoped scopes) (sp∷ arg rest) (ga , gr)
        with rename⇐ ren arg ga | rename-spine ren scopes rest gr
      ... | arg′ , ga′ | rest′ , gr′
        with cast⇐ refl (rename-local {locals = locals} {ty = T} scoped ρ) (arg′ , ga′)
      ... | typed , supported = sp∷ typed rest′ , supported , gr′

    -- A final checking derivation can supply a supported inference image.
    -- Holes remain transportable in checking mode but cannot close binders.
    check-infer : ∀ {n} {Γ : Ctx n} {t T}
      → Final t → (der : Γ ⊢ t ⇐ T) → Supported⇐ der → Infer Γ t T
    check-infer final (⇐-lam kind body) good = ⇒-lam kind body , good
    check-infer () ⇐-hole good
    check-infer final (⇐-infer der equal) good = ⇒-conv der equal , good
    check-infer final (⇐-conv der equal) good with check-infer final der good
    ... | typed , supported = ⇒-conv typed equal , supported
    check-infer final (⇐-cumul der le) good = ⇒-cumul der le , good

    -- Unlike an arbitrary native coherent substitution, these images
    -- carry the support needed for the restricted weakening theorem.
    Coherent : ∀ {n m} → Ctx n → Ctx m → Sub → Set
    Coherent {n} Γ Δ σ = ∀ (i : Fin n) → Infer Δ (σ (toℕ i)) (substS σ (lookup Γ i))

    forget-coherent : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ}
      → Coherent Γ Δ σ → C.Coherent Γ Δ σ
    forget-coherent coh i = proj₁ (coh i)

    lift-coherent : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ}
      → Coherent Γ Δ σ → ∀ T
      → Coherent (extend Γ T) (extend Δ (substS σ T)) (extSub σ)
    lift-coherent {σ = σ} coh T zero =
      cast⇒ refl (sym (subst-extSub-wk σ T)) (⇒-var zero , tt)
    lift-coherent {Γ = Γ} {Δ = Δ} {σ = σ} coh T (suc i) =
      cast⇒ refl
        (sym (trans (cong (substS (extSub σ)) (lookup-extend Γ T i))
          (subst-extSub-wk σ (lookup Γ i))))
        (rename⇒ (C.weakening Δ (substS σ T)) (proj₁ (coh i)) (proj₂ (coh i)))

    mutual
      subst⇒ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ t T}
        → Coherent Γ Δ σ → (der : Γ ⊢ t ⇒ T) → Supported⇒ der
        → Infer Δ (substS σ t) (substS σ T)
      subst⇒ coh (⇒-type level) good = ⇒-type level , tt
      subst⇒ coh (⇒-var i) good = coh i
      subst⇒ coh (⇒-pi d c) (gd , gc)
        with subst⇒ coh d gd | subst⇒ (lift-coherent coh _) c gc
      ... | d′ , gd′ | c′ , gc′ = ⇒-pi d′ c′ , gd′ , gc′
      subst⇒ coh (⇒-lam d b) (gd , gb)
        with subst⇒ coh d gd | subst⇐ (lift-coherent coh _) b gb
      ... | d′ , gd′ | b′ , gb′ = ⇒-lam d′ b′ , gd′ , gb′
      subst⇒ {σ = σ} coh (⇒-app {a = a} {c = c} f a-typed) (gf , ga)
        with subst⇒ coh f gf | subst⇒ coh a-typed ga
      ... | f′ , gf′ | a′ , ga′ =
        cast⇒ refl (sym (subst-topSub σ a c)) (⇒-app f′ a′ , gf′ , ga′)
      subst⇒ {σ = σ} coh (⇒-let {v = v} {T = T} ty val body) (gt , gv , gb)
        with subst⇒ coh ty gt | subst⇐ coh val gv | subst⇒ (lift-coherent coh _) body gb
      ... | ty′ , gt′ | val′ , gv′ | body′ , gb′ =
        cast⇒ refl (sym (subst-topSub σ v T)) (⇒-let ty′ val′ body′ , gt′ , gv′ , gb′)
      subst⇒ coh (⇒-global found) good =
        cast⇒ refl (sym (substS-closed (proj₁ (SignatureValid.global-type valid found))))
          (⇒-global found , tt)
      subst⇒ coh ⇒-int_type good = ⇒-int_type , tt
      subst⇒ coh ⇒-float_type good = ⇒-float_type , tt
      subst⇒ coh ⇒-binary_type good = ⇒-binary_type , tt
      subst⇒ coh ⇒-atom_type good = ⇒-atom_type , tt
      subst⇒ coh ⇒-int_lit good = ⇒-int_lit , tt
      subst⇒ coh ⇒-float_lit good = ⇒-float_lit , tt
      subst⇒ coh ⇒-atom_lit good = ⇒-atom_lit , tt
      subst⇒ coh (⇒-nat_lit builtin found ps is) good = ⇒-nat_lit builtin found ps is , tt
      subst⇒ coh (⇒-bounded_lit builtin found ps is) good = ⇒-bounded_lit builtin found ps is , tt
      subst⇒ {σ = σ} coh (⇒-data {ps = ps} found params indices) (gp , gi)
        with subst-spine coh (parameter-scope valid found) params gp
           | subst-spine coh (index-scope valid found params) indices gi
      ... | params′ , gp′ | indices′ , gi′
        with cast-arguments (substTerms-reverse σ ps) (indices′ , gi′)
      ... | i , gi = ⇒-data found params′ i , gp′ , gi
      subst⇒ {σ = σ} coh
        (⇒-ctor {ps = ps} found params fields) (gp , gf)
        with subst-spine coh (parameter-scope valid (SignatureValid.owner-visible valid found)) params gp
           | subst-spine coh (field-scope valid found params) fields gf
      ... | params′ , gp′ | fields′ , gf′
        with cast-arguments (substTerms-reverse σ ps) (fields′ , gf′)
      ... | f , gf =
        cast⇒ refl (sym (cong (tm-data _ (substTermsS σ ps))
          (C.registered-results-subst valid found params fields σ)))
          (⇒-ctor found params′ f , gp′ , gf)
      subst⇒ coh (⇒-case wf found s ps is mot branches covered) ()
      subst⇒ coh (⇒-effect_type t) good with subst⇒ coh t good
      ... | t′ , good′ = ⇒-effect_type t′ , good′
      subst⇒ coh (⇒-effect_pure t) good with subst⇒ coh t good
      ... | t′ , good′ = ⇒-effect_pure t′ , good′
      subst⇒ {σ = σ} coh (⇒-effect_bind {B = B} e k) (ge , gk)
        with subst⇒ coh e ge | subst⇒ coh k gk
      ... | e′ , ge′ | k′ , gk′
        with cast⇒ refl (cong (λ T → tm-pi _ _ (tm-effect_type T))
          (subst-extSub-wk σ B)) (k′ , gk′)
      ... | typed , supported = ⇒-effect_bind e′ typed , ge′ , supported
      subst⇒ {σ = σ} coh (⇒-conv t equal) good with subst⇒ coh t good
      ... | t′ , good′ = ⇒-conv t′ (≈-subst σ equal) , good′
      subst⇒ coh (⇒-cumul t le) good with subst⇒ coh t good
      ... | t′ , good′ = ⇒-cumul t′ le , good′

      subst⇐ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ t T}
        → Coherent Γ Δ σ → (der : Γ ⊢ t ⇐ T) → Supported⇐ der
        → Check Δ (substS σ t) (substS σ T)
      subst⇐ coh (⇐-lam d b) (gd , gb)
        with subst⇒ coh d gd | subst⇐ (lift-coherent coh _) b gb
      ... | d′ , gd′ | b′ , gb′ = ⇐-lam d′ b′ , gd′ , gb′
      subst⇐ coh ⇐-hole good = ⇐-hole , tt
      subst⇐ {σ = σ} coh (⇐-infer t equal) good with subst⇒ coh t good
      ... | t′ , good′ = ⇐-infer t′ (≈-subst σ equal) , good′
      subst⇐ {σ = σ} coh (⇐-conv t equal) good with subst⇐ coh t good
      ... | t′ , good′ = ⇐-conv t′ (≈-subst σ equal) , good′
      subst⇐ coh (⇐-cumul t le) good with subst⇒ coh t good
      ... | t′ , good′ = ⇐-cumul t′ le , good′

      subst-spine : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ locals args tele}
        → Coherent Γ Δ σ → ScopedTele (length locals) tele
        → (der : Spine Γ locals args tele) → SupportedSpine der
        → Arguments Δ (substTermsS σ locals) (substTermsS σ args) tele
      subst-spine coh tele[] sp[] good = sp[] , tt
      subst-spine {σ = σ} {locals = locals} coh
        (tele∷ {ty = T} scoped scopes) (sp∷ arg rest) (ga , gr)
        with subst⇐ coh arg ga | subst-spine coh scopes rest gr
      ... | arg′ , ga′ | rest′ , gr′
        with cast⇐ refl (subst-local {locals = locals} {ty = T} scoped σ) (arg′ , ga′)
      ... | typed , supported = sp∷ typed rest′ , supported , gr′

    identity : ∀ {n} (Γ : Ctx n) → Coherent Γ Γ F.identity
    identity Γ i = cast⇒ refl (sym (substS-idSub (lookup Γ i))) (⇒-var i , tt)

    push-coherent : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ T arg}
      → Coherent Δ Γ σ → Infer Γ arg (substS σ T)
      → Coherent (extend Δ T) Γ (F.push arg σ)
    push-coherent {σ = σ} {T = T} {arg = arg} coh checked zero =
      cast⇒ refl (sym (push-undoes-wk arg σ T)) checked
    push-coherent {Δ = Δ} {σ = σ} {T = T} {arg = arg} coh checked (suc i) =
      cast⇒ refl (sym (trans
        (cong (substS (F.push arg σ)) (lookup-extend Δ T i))
        (push-undoes-wk arg σ (lookup Δ i)))) (coh i)

    top-coherent : ∀ {n} {Γ : Ctx n} {arg T}
      → Infer Γ arg T → Coherent (extend Γ T) Γ (topSub arg)
    top-coherent {Γ = Γ} {arg = arg} {T = T} checked =
      subst (Coherent (extend Γ T) Γ)
        (funext (λ { zero → refl ; (suc i) → refl }))
        (push-coherent (identity Γ) (cast⇒ refl (sym (substS-idSub T)) checked))

    instantiate-coherent : ∀ {n d e} {Γ : Ctx n} {Δ : Ctx d} {Ε : Ctx e}
      {locals args tele}
      → Declared Δ tele Ε → (actual : Spine Γ locals args tele)
      → SupportedSpine actual → FinalTerms args
      → Coherent Δ Γ (F.prefix locals F.identity)
      → Coherent Ε Γ (F.advance args (F.prefix locals F.identity))
    instantiate-coherent dt[] sp[] good ft[] coh = coh
    instantiate-coherent {locals = locals}
      (dt∷ {T = T} scope kind rest) (sp∷ {arg = arg} checked args)
      (ga , gr) (ft∷ final finals) coh =
      instantiate-coherent rest args gr finals
        (push-coherent coh
          (cast⇒ refl (sym (Frames.prefix-agrees locals T)) (check-infer final checked ga)))

    result-frame : ∀ {n p f} {Γ : Ctx n} {Π : Ctx p} {Φ : Ctx f}
      {ps args ptele ftele}
      → Declared ⟨⟩ ptele Π → Declared Π ftele Φ
      → (pa : Spine Γ [] ps ptele) → (fa : Spine Γ (reverse ps) args ftele)
      → SupportedSpine pa → SupportedSpine fa → FinalTerms ps → FinalTerms args
      → Coherent Φ Γ (F.advance args (F.advance ps F.identity))
    result-frame {Γ = Γ} {Π = Π} {Φ = Φ} {ps = ps} {args = args}
      pd fd pa fa gp gf fp ff =
      subst (λ σ → Coherent Φ Γ (F.advance args σ))
        (sym (funext (F.advance-reverse ps F.identity)))
        (instantiate-coherent fd fa gf ff
          (subst (Coherent Π Γ) (funext (F.advance-reverse ps F.identity))
            (instantiate-coherent pd pa gp fp (λ ()))))

    registered-frame : ∀ {n} {Γ : Ctx n} {name family ctor ps args}
      → (found : findCtor name (IndEnv.families ind) ≡ just (family , ctor))
      → (pa : Spine Γ [] ps (fam-params family))
      → (fa : Spine Γ (reverse ps) args (ctor-args ctor))
      → SupportedSpine pa → SupportedSpine fa → FinalTerms ps → FinalTerms args
      → Coherent (ConstructorDeclaration.field-context
          (SignatureValid.constructor-declared valid found)) Γ
          (F.advance args (F.advance ps F.identity))
    registered-frame found pa fa gp gf fp ff = result-frame
      (ConstructorDeclaration.parameters (SignatureValid.constructor-declared valid found))
      (ConstructorDeclaration.fields (SignatureValid.constructor-declared valid found)) pa fa gp gf fp ff

    close-coherent : ∀ {n d m} {Γ : Ctx n} {Δ : Ctx d} {Θ : Ctx m}
      {σ τ locals args tele}
      → Native.Opened Δ σ tele Θ → (actual : Spine Γ locals args tele)
      → SupportedSpine actual → FinalTerms args → Coherent Δ Γ τ
      → (∀ i → Proof.Substitution.substCompose τ σ i ≡ F.prefix locals F.identity i)
      → Coherent Θ Γ (F.advance args τ)
    close-coherent Native.op[] sp[] good ft[] coh equal = coh
    close-coherent {σ = σ} {τ = τ} {locals = locals}
      (Native.op∷ {T = T} opening) (sp∷ {arg = arg} checked args)
      (ga , gr) (ft∷ final finals) coh equal =
      close-coherent opening args gr finals
        (push-coherent coh (cast⇒ refl (sym expected) (check-infer final checked ga)))
        (Frames.push-compose arg τ σ locals equal)
      where
        expected : substS τ (substS σ T) ≡ F.instantiatePrefix locals T
        expected = trans (Proof.Substitution.subst-compose τ σ T)
          (trans (cong (λ ρ → substS ρ T) (funext equal)) (Frames.prefix-agrees locals T))

    branch-frame : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {ps args tele}
      → Native.Opened Γ (F.advance ps F.identity) tele Θ
      → (actual : Spine Γ (reverse ps) args tele)
      → SupportedSpine actual → FinalTerms args
      → Coherent Θ Γ (F.advance args F.identity)
    branch-frame {Γ = Γ} {ps = ps} opening actual good finals =
      close-coherent opening actual good finals (identity Γ)
        (λ i → trans (substS-idSub (F.advance ps F.identity i)) (F.advance-reverse ps F.identity i))

    -- This closes an arbitrary supported body in the fresh ambient
    -- branch context. It is not preservation of a whole source case.
    contract-branch : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {ps args tele b T}
      → Native.Opened Γ (F.advance ps F.identity) tele Θ
      → (actual : Spine Γ (reverse ps) args tele)
      → SupportedSpine actual → FinalTerms args
      → (checked : Θ ⊢ b ⇐ T) → Supported⇐ checked
      → Check Γ (Core.Reduction.substArgs args b) (Core.Reduction.substArgs args T)
    contract-branch {ps = ps} {args = args} {b = b} {T = T} opening actual good finals checked gb =
      cast⇐ (F.fields-agree args b) (F.fields-agree args T)
        (subst⇐ (branch-frame {ps = ps} opening actual good finals) checked gb)
