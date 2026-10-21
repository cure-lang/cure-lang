------------------------------------------------------------------------
-- General native transport, including nested cases and native WF suffixes.
-- Target callers are well formed; source branch WF proofs are traversed
-- structurally. No fragment certificate or WF/preservation callback.
------------------------------------------------------------------------
module Proof.DependentGeneralTransport where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-comm; suc-injective)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Data.List.Properties using (length-reverse; length-++)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
open import Core.Signature
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; ⟨⟩; extend; lookup; lookup-extend; Conversion)
open import Core.Coverage using (case-coverage-rename; case-coverage-subst)
open import Core.Verification using (ScopedTele; tele[]; tele∷)
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentCoherence as Frames
import Proof.DependentTransport as Fragment
import Proof.DependentScoping as Scope
import Proof.DependentScopedAlgebra as A
import Proof.DependentContextSuffix as Suffix
open import Proof.Substitution
  using (renameSub; substCompose; rename-topSub; subst-topSub; rename-closed; substS-closed;
         renameTerms-reverse; substTerms-reverse; subst-extSub-wk)
open import Proof.Substitution using (substS-idSub)
open import Proof.Progress using (FinalTerms)
open import Proof.LocalFrame using (rename-local; subst-local)

same-context : ∀ {n} {Γ Δ : Ctx n}
  → _≡_ {A = Suffix.AnyCtx} (n , Γ) (n , Δ) → Γ ≡ Δ
same-context refl = refl

length-snoc : ∀ (tele : Telescope) name T → length (tele ++ ((name , T) ∷ [])) ≡ suc (length tele)
length-snoc tele name T =
  trans (length-++ tele) (trans (+-suc (length tele) 0) (cong suc (+-identityʳ (length tele))))

module General (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv
  module C = Frames.NativeFrames ind sig conv
  module Sc = Scope.Scoping ind sig conv
  module D = Fragment.Transport ind sig conv
  open C using (Renaming; index; agrees; types)
  open Conversion conv

  cast⇒ : ∀ {n} {Γ : Ctx n} {t t′ T T′}
    → t ≡ t′ → T ≡ T′ → Γ ⊢ t ⇒ T → Γ ⊢ t′ ⇒ T′
  cast⇒ refl refl typed = typed
  cast⇐ : ∀ {n} {Γ : Ctx n} {t t′ T T′}
    → t ≡ t′ → T ≡ T′ → Γ ⊢ t ⇐ T → Γ ⊢ t′ ⇐ T′
  cast⇐ refl refl typed = typed

  source-renaming : ∀ {n m d} {Γ : Ctx n} {Θ : Ctx m} {Δ : Ctx d} {ρ}
    → _≡_ {A = Suffix.AnyCtx} (n , Γ) (m , Θ) → Renaming Θ Δ ρ → Renaming Γ Δ ρ
  source-renaming refl ren = ren

  source-coherent : ∀ {n m d} {Γ : Ctx n} {Θ : Ctx m} {Δ : Ctx d} {σ}
    → _≡_ {A = Suffix.AnyCtx} (n , Γ) (m , Θ)
    → C.Coherent Θ Δ σ → C.Coherent Γ Δ σ
  source-coherent refl coh = coh

  module Valid (valid : SignatureValid) where
    index-scoping : ∀ {n} {Γ : Ctx n} {name family ps}
      → findFamily name (IndEnv.families ind) ≡ just family
      → Spine Γ [] ps (fam-params family)
      → ScopedTele (length ps) (fam-indices family)
    index-scoping {ps = ps} found params =
      subst (λ n → ScopedTele n _) (length-reverse ps) (D.index-scope valid found params)
    field-scoping : ∀ {n} {Γ : Ctx n} {name family ctor ps}
      → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
      → Spine Γ [] ps (fam-params family)
      → ScopedTele (length ps) (ctor-args ctor)
    field-scoping {ps = ps} found params =
      subst (λ n → ScopedTele n _) (length-reverse ps) (D.field-scope valid found params)
    result-scoping : ∀ {n} {Γ : Ctx n} {name family ctor ps}
      → findCtor name (IndEnv.families ind) ≡ just (family , ctor)
      → Spine Γ [] ps (fam-params family)
      → ScopedTerms (length ps + length (ctor-args ctor)) (ctor-indices ctor)
    result-scoping {ctor = ctor} {ps = ps} found params =
      subst (λ n → ScopedTerms n (ctor-indices ctor)) (sym size)
        (proj₂ (ConstructorDeclaration.result-scoping declaration))
      where
        declaration = SignatureValid.constructor-declared valid found
        size = trans (+-comm (length ps) (length (ctor-args ctor)))
          (trans (cong (length (ctor-args ctor) +_)
            (trans (spine-length params) (D.declaration-size (ConstructorDeclaration.parameters declaration))))
            (C.declared-length (ConstructorDeclaration.fields declaration)))

    mutual
      rename⇒ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ t T}
        → Renaming Γ Δ ρ → WellFormed Δ → Γ ⊢ t ⇒ T
        → Δ ⊢ rename ρ t ⇒ rename ρ T
      rename⇒ ren wf (⇒-type level) = ⇒-type level
      rename⇒ ren wf (⇒-var i) = cast⇒
        (cong tm-var (agrees ren i)) (types ren i) (⇒-var (index ren i))
      rename⇒ ren wf (⇒-pi d c) with rename⇒ ren wf d
      ... | d′ = ⇒-pi d′
        (rename⇒ (C.extend-renaming ren _) (wf∷ wf (Sc.infer-scoped d′) d′) c)
      rename⇒ ren wf (⇒-lam d b) with rename⇒ ren wf d
      ... | d′ = ⇒-lam d′
        (rename⇐ (C.extend-renaming ren _) (wf∷ wf (Sc.infer-scoped d′) d′) b)
      rename⇒ {ρ = ρ} ren wf (⇒-app {a = a} {c = c} f arg) =
        cast⇒ refl (sym (rename-topSub ρ a c)) (⇒-app (rename⇒ ren wf f) (rename⇒ ren wf arg))
      rename⇒ {ρ = ρ} ren wf (⇒-let {v = v} {T = T} ty value body) with rename⇒ ren wf ty
      ... | ty′ = cast⇒ refl (sym (rename-topSub ρ v T))
        (⇒-let ty′ (rename⇐ ren wf value)
          (rename⇒ (C.extend-renaming ren _) (wf∷ wf (Sc.infer-scoped ty′) ty′) body))
      rename⇒ ren wf (⇒-global found) =
        cast⇒ refl (sym (rename-closed (proj₁ (SignatureValid.global-type valid found)))) (⇒-global found)
      rename⇒ ren wf ⇒-int_type = ⇒-int_type
      rename⇒ ren wf ⇒-float_type = ⇒-float_type
      rename⇒ ren wf ⇒-binary_type = ⇒-binary_type
      rename⇒ ren wf ⇒-atom_type = ⇒-atom_type
      rename⇒ ren wf ⇒-int_lit = ⇒-int_lit
      rename⇒ ren wf ⇒-float_lit = ⇒-float_lit
      rename⇒ ren wf ⇒-atom_lit = ⇒-atom_lit
      rename⇒ ren wf (⇒-nat_lit builtin found ps is) = ⇒-nat_lit builtin found ps is
      rename⇒ ren wf (⇒-bounded_lit builtin found ps is) = ⇒-bounded_lit builtin found ps is
      rename⇒ {ρ = ρ} ren wf (⇒-data {ps = ps} found params indices) =
        ⇒-data found (rename-spine ren wf (D.parameter-scope valid found) params)
          (subst (λ locals → Spine _ locals _ _) (renameTerms-reverse ρ ps)
            (rename-spine ren wf (D.index-scope valid found params) indices))
      rename⇒ {ρ = ρ} ren wf (⇒-ctor {ps = ps} found params fields) =
        cast⇒ refl (sym (cong (tm-data _ (renameTerms ρ ps))
          (C.registered-results-rename valid found params fields ρ)))
          (⇒-ctor found
            (rename-spine ren wf (D.parameter-scope valid (SignatureValid.owner-visible valid found)) params)
            (subst (λ locals → Spine _ locals _ _) (renameTerms-reverse ρ ps)
              (rename-spine ren wf (D.field-scope valid found params) fields)))
      rename⇒ {ρ = ρ} ren wf
        (⇒-case {s = s} {motive = mot} {ps = ps} {is = is} source-wf found scrutinee params indices mot-typed brs covered) =
        cast⇒ refl (sym (A.rename-case-goal ρ mot is s))
          (⇒-case wf found (rename⇒ ren wf scrutinee)
            (rename-spine ren wf (D.parameter-scope valid found) params)
            (subst (λ locals → Spine _ locals _ _) (renameTerms-reverse ρ ps)
              (rename-spine ren wf (D.index-scope valid found params) indices))
            (rename-motive ren wf (index-scoping found params) mot-typed)
            (rename-branches ren wf params brs) (case-coverage-rename ρ covered))
      rename⇒ ren wf (⇒-effect_type t) = ⇒-effect_type (rename⇒ ren wf t)
      rename⇒ ren wf (⇒-effect_pure t) = ⇒-effect_pure (rename⇒ ren wf t)
      rename⇒ {ρ = ρ} ren wf (⇒-effect_bind {B = B} e k) =
        ⇒-effect_bind (rename⇒ ren wf e)
          (cast⇒ refl (cong (λ T → tm-pi _ _ (tm-effect_type T))
            (sym (ext-wk-rename ρ B))) (rename⇒ ren wf k))
      rename⇒ {ρ = ρ} ren wf (⇒-conv typed equal) = ⇒-conv (rename⇒ ren wf typed) (≈-rename ρ equal)
      rename⇒ ren wf (⇒-cumul typed le) = ⇒-cumul (rename⇒ ren wf typed) le

      rename⇐ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ t T}
        → Renaming Γ Δ ρ → WellFormed Δ → Γ ⊢ t ⇐ T
        → Δ ⊢ rename ρ t ⇐ rename ρ T
      rename⇐ ren wf (⇐-lam d b) with rename⇒ ren wf d
      ... | d′ = ⇐-lam d′
        (rename⇐ (C.extend-renaming ren _) (wf∷ wf (Sc.infer-scoped d′) d′) b)
      rename⇐ ren wf ⇐-hole = ⇐-hole
      rename⇐ {ρ = ρ} ren wf (⇐-infer typed equal) = ⇐-infer (rename⇒ ren wf typed) (≈-rename ρ equal)
      rename⇐ {ρ = ρ} ren wf (⇐-conv typed equal) = ⇐-conv (rename⇐ ren wf typed) (≈-rename ρ equal)
      rename⇐ ren wf (⇐-cumul typed le) = ⇐-cumul (rename⇒ ren wf typed) le

      rename-spine : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ locals args tele}
        → Renaming Γ Δ ρ → WellFormed Δ → ScopedTele (length locals) tele
        → Spine Γ locals args tele → Spine Δ (renameTerms ρ locals) (renameTerms ρ args) tele
      rename-spine ren wf tele[] sp[] = sp[]
      rename-spine {ρ = ρ} {locals = locals} ren wf (tele∷ {ty = T} scoped scopes) (sp∷ arg rest) =
        sp∷ (cast⇐ refl (rename-local {locals = locals} {ty = T} scoped ρ) (rename⇐ ren wf arg))
          (rename-spine ren wf scopes rest)

      rename-motive : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ family ps mot level}
        → Renaming Γ Δ ρ → WellFormed Δ → ScopedTele (length ps) (fam-indices family)
        → Motive Γ family ps mot level → Motive Δ family (renameTerms ρ ps) (rename ρ mot) level
      rename-motive {ρ = ρ} {family = family} {ps = ps} {level = level}
        ren wf scoped (motive scope kind typed) =
        motive (Sc.infer-scoped typed′)
          (cast⇒ (A.rename-motiveType ρ family ps level scoped) refl (rename⇒ ren wf kind)) typed′
        where
          typed′ = cast⇒ refl (A.rename-motiveType ρ family ps level scoped) (rename⇒ ren wf typed)

      rename-branches : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ family ps mot brs}
        → Renaming Γ Δ ρ → WellFormed Δ → Spine Γ [] ps (fam-params family)
        → Branches Γ family ps mot brs
        → Branches Δ family (renameTerms ρ ps) (rename ρ mot) (renameBranches ρ brs)
      rename-branches ren wf params br[] = br[]
      rename-branches {ρ = ρ} {ps = ps} {mot = mot} ren wf params
        (br∷ {name = name} {ctor = ctor} found refl opening branch-wf body rest)
        with rename-opening branch-wf (Suffix.opened-snoc opening) refl ren wf
      ... | size , Ω , wfΩ , opening′ , ren′ =
        br∷ found refl
          (A.opened-agree (field-scoping found params) (A.rename-frame-agrees ρ ps) opening′) wfΩ
          (cast⇐ refl (A.rename-branchGoal ρ name ps ctor mot (result-scoping found params))
            (rename⇐ ren′ wfΩ body))
          (rename-branches ren wf params rest)

      -- Explicit endpoint equality lets the ORIGINAL wf∷ be matched
      -- directly, retaining its kind proof as a strict recursive subterm.
      rename-opening : ∀ {n m d k} {Γ : Ctx n} {Θ : Ctx m} {Δ : Ctx d} {Ξ : Ctx k} {ρ σ tele}
        → WellFormed Θ → Suffix.OpenedSnoc Γ σ tele Ξ
        → _≡_ {A = Suffix.AnyCtx} (m , Θ) (k , Ξ)
        → Renaming Γ Δ ρ → WellFormed Δ
        → Σ ℕ (λ l → Σ (Ctx l) (λ Ω → WellFormed Ω
            × Native.Opened Δ (renameSub ρ σ) tele Ω
            × Renaming Θ Ω (ext^ (length tele) ρ)))
      rename-opening {Δ = Δ} wf Suffix.os[] equal ren target-wf =
        _ , Δ , target-wf , Native.op[] , source-renaming equal ren
      rename-opening wf[] (Suffix.os∷ rest) () ren target-wf
      rename-opening {ρ = ρ} {σ = σ}
        (wf∷ {Γ = Γ₀} {T = U} wf scoped kind)
        (Suffix.os∷ {Θ = Ξ₀} {tele = tele} {name = name} {T = T} rest) equal ren target-wf
        with suc-injective (cong proj₁ equal)
      ... | refl with Suffix.extend-injective {Γ = Γ₀} {Δ = Ξ₀}
        {T = U} {U = substS (extSub^ (length tele) σ) T} (same-context equal)
      ... | refl , refl with rename-opening wf rest refl ren target-wf
      ... | size , Ω , wfΩ , opening′ , ren′ with rename⇒ ren′ wfΩ kind
      ... | kind′ =
        _ , extend Ω _ , wf∷ wfΩ (Sc.infer-scoped kind′) kind′ ,
        Suffix.append-renamed {ρ = ρ} {σ = σ} opening′ name T ,
        subst (λ ar → Renaming _ _ (ext^ ar ρ)) (sym (length-snoc tele name T))
          (C.extend-renaming ren′ _)

    -- Images are unrestricted native inference derivations. The target
    -- extension has an actual native WF proof, not a support certificate.
    lift-coherent : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ}
      → C.Coherent Γ Δ σ → ∀ T
      → WellFormed (extend Δ (substS σ T))
      → C.Coherent (extend Γ T) (extend Δ (substS σ T)) (extSub σ)
    lift-coherent {σ = σ} coh T wf zero =
      cast⇒ refl (sym (subst-extSub-wk σ T)) (⇒-var zero)
    lift-coherent {Γ = Γ} {Δ = Δ} {σ = σ} coh T wf (suc i) =
      cast⇒ refl
        (sym (trans (cong (substS (extSub σ)) (lookup-extend Γ T i))
          (subst-extSub-wk σ (lookup Γ i))))
        (rename⇒ (C.weakening Δ (substS σ T)) wf (coh i))

    mutual
      subst⇒ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ t T}
        → C.Coherent Γ Δ σ → WellFormed Δ → Γ ⊢ t ⇒ T
        → Δ ⊢ substS σ t ⇒ substS σ T
      subst⇒ coh wf (⇒-type level) = ⇒-type level
      subst⇒ coh wf (⇒-var i) = coh i
      subst⇒ coh wf (⇒-pi d c) with subst⇒ coh wf d
      ... | d′ = ⇒-pi d′
        (subst⇒ (lift-coherent coh _ (wf∷ wf (Sc.infer-scoped d′) d′))
          (wf∷ wf (Sc.infer-scoped d′) d′) c)
      subst⇒ coh wf (⇒-lam d b) with subst⇒ coh wf d
      ... | d′ = ⇒-lam d′
        (subst⇐ (lift-coherent coh _ (wf∷ wf (Sc.infer-scoped d′) d′))
          (wf∷ wf (Sc.infer-scoped d′) d′) b)
      subst⇒ {σ = σ} coh wf (⇒-app {a = a} {c = c} f arg) =
        cast⇒ refl (sym (subst-topSub σ a c)) (⇒-app (subst⇒ coh wf f) (subst⇒ coh wf arg))
      subst⇒ {σ = σ} coh wf (⇒-let {v = v} {T = T} ty value body) with subst⇒ coh wf ty
      ... | ty′ = cast⇒ refl (sym (subst-topSub σ v T))
        (⇒-let ty′ (subst⇐ coh wf value)
          (subst⇒ (lift-coherent coh _ (wf∷ wf (Sc.infer-scoped ty′) ty′))
            (wf∷ wf (Sc.infer-scoped ty′) ty′) body))
      subst⇒ coh wf (⇒-global found) =
        cast⇒ refl (sym (substS-closed (proj₁ (SignatureValid.global-type valid found)))) (⇒-global found)
      subst⇒ coh wf ⇒-int_type = ⇒-int_type
      subst⇒ coh wf ⇒-float_type = ⇒-float_type
      subst⇒ coh wf ⇒-binary_type = ⇒-binary_type
      subst⇒ coh wf ⇒-atom_type = ⇒-atom_type
      subst⇒ coh wf ⇒-int_lit = ⇒-int_lit
      subst⇒ coh wf ⇒-float_lit = ⇒-float_lit
      subst⇒ coh wf ⇒-atom_lit = ⇒-atom_lit
      subst⇒ coh wf (⇒-nat_lit builtin found ps is) = ⇒-nat_lit builtin found ps is
      subst⇒ coh wf (⇒-bounded_lit builtin found ps is) = ⇒-bounded_lit builtin found ps is
      subst⇒ {σ = σ} coh wf (⇒-data {ps = ps} found params indices) =
        ⇒-data found (subst-spine coh wf (D.parameter-scope valid found) params)
          (subst (λ locals → Spine _ locals _ _) (substTerms-reverse σ ps)
            (subst-spine coh wf (D.index-scope valid found params) indices))
      subst⇒ {σ = σ} coh wf (⇒-ctor {ps = ps} found params fields) =
        cast⇒ refl (sym (cong (tm-data _ (substTermsS σ ps))
          (C.registered-results-subst valid found params fields σ)))
          (⇒-ctor found
            (subst-spine coh wf (D.parameter-scope valid (SignatureValid.owner-visible valid found)) params)
            (subst (λ locals → Spine _ locals _ _) (substTerms-reverse σ ps)
              (subst-spine coh wf (D.field-scope valid found params) fields)))
      subst⇒ {σ = σ} coh wf
        (⇒-case {s = s} {motive = mot} {ps = ps} {is = is} source-wf found scrutinee params indices mot-typed brs covered) =
        cast⇒ refl (sym (A.subst-case-goal σ mot is s))
          (⇒-case wf found (subst⇒ coh wf scrutinee)
            (subst-spine coh wf (D.parameter-scope valid found) params)
            (subst (λ locals → Spine _ locals _ _) (substTerms-reverse σ ps)
              (subst-spine coh wf (D.index-scope valid found params) indices))
            (subst-motive coh wf (index-scoping found params) mot-typed)
            (subst-branches coh wf params brs) (case-coverage-subst σ covered))
      subst⇒ coh wf (⇒-effect_type t) = ⇒-effect_type (subst⇒ coh wf t)
      subst⇒ coh wf (⇒-effect_pure t) = ⇒-effect_pure (subst⇒ coh wf t)
      subst⇒ {σ = σ} coh wf (⇒-effect_bind {B = B} e k) =
        ⇒-effect_bind (subst⇒ coh wf e)
          (cast⇒ refl (cong (λ T → tm-pi _ _ (tm-effect_type T))
            (subst-extSub-wk σ B)) (subst⇒ coh wf k))
      subst⇒ {σ = σ} coh wf (⇒-conv typed equal) = ⇒-conv (subst⇒ coh wf typed) (≈-subst σ equal)
      subst⇒ coh wf (⇒-cumul typed le) = ⇒-cumul (subst⇒ coh wf typed) le

      subst⇐ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ t T}
        → C.Coherent Γ Δ σ → WellFormed Δ → Γ ⊢ t ⇐ T
        → Δ ⊢ substS σ t ⇐ substS σ T
      subst⇐ coh wf (⇐-lam d b) with subst⇒ coh wf d
      ... | d′ = ⇐-lam d′
        (subst⇐ (lift-coherent coh _ (wf∷ wf (Sc.infer-scoped d′) d′))
          (wf∷ wf (Sc.infer-scoped d′) d′) b)
      subst⇐ coh wf ⇐-hole = ⇐-hole
      subst⇐ {σ = σ} coh wf (⇐-infer typed equal) = ⇐-infer (subst⇒ coh wf typed) (≈-subst σ equal)
      subst⇐ {σ = σ} coh wf (⇐-conv typed equal) = ⇐-conv (subst⇐ coh wf typed) (≈-subst σ equal)
      subst⇐ coh wf (⇐-cumul typed le) = ⇐-cumul (subst⇒ coh wf typed) le

      subst-spine : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ locals args tele}
        → C.Coherent Γ Δ σ → WellFormed Δ → ScopedTele (length locals) tele
        → Spine Γ locals args tele → Spine Δ (substTermsS σ locals) (substTermsS σ args) tele
      subst-spine coh wf tele[] sp[] = sp[]
      subst-spine {σ = σ} {locals = locals} coh wf (tele∷ {ty = T} scoped scopes) (sp∷ arg rest) =
        sp∷ (cast⇐ refl (subst-local {locals = locals} {ty = T} scoped σ) (subst⇐ coh wf arg))
          (subst-spine coh wf scopes rest)

      subst-motive : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ family ps mot level}
        → C.Coherent Γ Δ σ → WellFormed Δ → ScopedTele (length ps) (fam-indices family)
        → Motive Γ family ps mot level → Motive Δ family (substTermsS σ ps) (substS σ mot) level
      subst-motive {σ = σ} {family = family} {ps = ps} {level = level}
        coh wf scoped (motive scope kind typed) =
        motive (Sc.infer-scoped typed′)
          (cast⇒ (A.subst-motiveType σ family ps level scoped) refl (subst⇒ coh wf kind)) typed′
        where
          typed′ = cast⇒ refl (A.subst-motiveType σ family ps level scoped) (subst⇒ coh wf typed)

      subst-branches : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ family ps mot brs}
        → C.Coherent Γ Δ σ → WellFormed Δ → Spine Γ [] ps (fam-params family)
        → Branches Γ family ps mot brs
        → Branches Δ family (substTermsS σ ps) (substS σ mot) (substBranchesS σ brs)
      subst-branches coh wf params br[] = br[]
      subst-branches {σ = σ} {ps = ps} {mot = mot} coh wf params
        (br∷ {name = name} {ctor = ctor} found refl opening branch-wf body rest)
        with subst-opening branch-wf (Suffix.opened-snoc opening) refl coh wf
      ... | size , Ω , wfΩ , opening′ , coh′ =
        br∷ found refl
          (A.opened-agree (field-scoping found params) (A.subst-frame-agrees σ ps) opening′) wfΩ
          (cast⇐ refl (A.subst-branchGoal σ name ps ctor mot (result-scoping found params))
            (subst⇐ coh′ wfΩ body))
          (subst-branches coh wf params rest)

      subst-opening : ∀ {n m d k} {Γ : Ctx n} {Θ : Ctx m} {Δ : Ctx d} {Ξ : Ctx k} {τ σ tele}
        → WellFormed Θ → Suffix.OpenedSnoc Γ σ tele Ξ
        → _≡_ {A = Suffix.AnyCtx} (m , Θ) (k , Ξ)
        → C.Coherent Γ Δ τ → WellFormed Δ
        → Σ ℕ (λ l → Σ (Ctx l) (λ Ω → WellFormed Ω
            × Native.Opened Δ (substCompose τ σ) tele Ω
            × C.Coherent Θ Ω (extSub^ (length tele) τ)))
      subst-opening {Δ = Δ} wf Suffix.os[] equal coh target-wf =
        _ , Δ , target-wf , Native.op[] , source-coherent equal coh
      subst-opening wf[] (Suffix.os∷ rest) () coh target-wf
      subst-opening {τ = τ} {σ = σ}
        (wf∷ {Γ = Γ₀} {T = U} wf scoped kind)
        (Suffix.os∷ {Θ = Ξ₀} {tele = tele} {name = name} {T = T} rest) equal coh target-wf
        with suc-injective (cong proj₁ equal)
      ... | refl with Suffix.extend-injective {Γ = Γ₀} {Δ = Ξ₀}
        {T = U} {U = substS (extSub^ (length tele) σ) T} (same-context equal)
      ... | refl , refl with subst-opening wf rest refl coh target-wf
      ... | size , Ω , wfΩ , opening′ , coh′ with subst⇒ coh′ wfΩ kind
      ... | kind′ =
        _ , extend Ω _ , wf∷ wfΩ (Sc.infer-scoped kind′) kind′ ,
        Suffix.append-substituted {τ = τ} {σ = σ} opening′ name T ,
        subst (λ ar → C.Coherent
          (extend Γ₀ (substS (extSub^ (length tele) σ) T))
          (extend Ω (substS (extSub^ (length tele) τ)
            (substS (extSub^ (length tele) σ) T))) (extSub^ ar τ))
          (sym (length-snoc tele name T))
          (lift-coherent {Γ = Γ₀} {Δ = Ω} {σ = extSub^ (length tele) τ}
            coh′ (substS (extSub^ (length tele) σ) T) (wf∷ wfΩ (Sc.infer-scoped kind′) kind′))

    Contexts : ∀ {n} → Ctx n → Ctx n → Set
    Contexts {n} Γ Δ = ∀ (i : Fin n) → lookup Γ i ≈ lookup Δ i

    context-coherent : ∀ {n} {Γ Δ : Ctx n} → Contexts Γ Δ → C.Coherent Γ Δ F.identity
    context-coherent {Γ = Γ} equal i =
      cast⇒ refl (sym (substS-idSub (lookup Γ i))) (⇒-conv (⇒-var i) (≈-sym (equal i)))

    context⇒ : ∀ {n} {Γ Δ : Ctx n} {t T}
      → Contexts Γ Δ → WellFormed Δ → Γ ⊢ t ⇒ T → Δ ⊢ t ⇒ T
    context⇒ {Γ = Γ} {Δ = Δ} {t = t} {T = T} equal wf typed =
      cast⇒ (substS-idSub t) (substS-idSub T)
        (subst⇒ (context-coherent {Γ = Γ} {Δ = Δ} equal) wf typed)
    context⇐ : ∀ {n} {Γ Δ : Ctx n} {t T}
      → Contexts Γ Δ → WellFormed Δ → Γ ⊢ t ⇐ T → Δ ⊢ t ⇐ T
    context⇐ {Γ = Γ} {Δ = Δ} {t = t} {T = T} equal wf typed =
      cast⇐ (substS-idSub t) (substS-idSub T)
        (subst⇐ (context-coherent {Γ = Γ} {Δ = Δ} equal) wf typed)

    binder-context : ∀ {n} {Γ : Ctx n} {T U}
      → T ≈ U → Contexts (extend Γ T) (extend Γ U)
    binder-context equal zero = ≈-rename wk equal
    binder-context equal (suc i) = ≈-refl

    top-coherent : ∀ {n} {Γ : Ctx n} {arg T}
      → Γ ⊢ arg ⇒ T → C.Coherent (extend Γ T) Γ (topSub arg)
    top-coherent {Γ = Γ} {arg = arg} {T = T} checked =
      subst (C.Coherent (extend Γ T) Γ)
        (funext (λ { zero → refl ; (suc i) → refl }))
        (C.push-coherent (C.identity Γ) (cast⇒ refl (sym (substS-idSub T)) checked))

    -- Unlike the earlier fragment theorem, BOTH the substituted body and
    -- the field images may contain arbitrarily nested native cases.
    contract-branch : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {ps args tele b T}
      → WellFormed Γ → Native.Opened Γ (F.advance ps F.identity) tele Θ
      → Spine Γ (reverse ps) args tele → FinalTerms args
      → Θ ⊢ b ⇐ T
      → Γ ⊢ Core.Reduction.substArgs args b ⇐ Core.Reduction.substArgs args T
    contract-branch {ps = ps} {args = args} {b = b} {T = T} wf opening actual finals checked =
      cast⇐ (F.fields-agree args b) (F.fields-agree args T)
        (subst⇐ (C.branch-frame {ps = ps} opening actual finals) wf checked)
