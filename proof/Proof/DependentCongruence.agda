------------------------------------------------------------------------
-- One-layer native congruence closures, NOT recursive subject reduction.
-- Local child endpoint typings are explicit. rc only connects RAW steps
-- with conversion; it contains no typing or preservation oracle.
------------------------------------------------------------------------
module Proof.DependentCongruence where

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (_⊔ˡ_)
open import Core.Signature
open import Core.Reduction
open import Core.Coverage using (CaseCoverage; case-coverage-reduce)
open import Core.Typing using (Ctx; extend; Conversion; All2; a2[]; a2∷)
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentScoping as Scope
import Proof.DependentGeneralTransport as General
import Proof.DependentSpineConversion as SpineConversion
import Proof.DependentConstructorInversion as Inversion

module Laws (ind : IndEnv) (sig : Signature) (conv : Conversion)
  (valid : Native.Typing.SignatureValid ind sig conv)
  (rc : ∀ {t u} → _⇝_ sig t u → Conversion._≈_ conv t u) where
  open Native.Typing ind sig conv
  open Conversion conv
  module S = SpineConversion.Laws ind sig conv
  module G = General.General ind sig conv
  module GV = G.Valid valid
  module Sc = Scope.Scoping ind sig conv
  module I = Inversion.Laws ind sig conv

  -- The selected expected type belongs to the ORIGINAL dependent spine;
  -- all preceding fields are unchanged at the selected position.
  expected-at : ∀ {n} {Γ : Ctx n} {locals args tele}
    → Spine Γ locals args tele → Fin (len args) → Term
  expected-at (sp∷ {locals = locals} {T = T} checked rest) zero =
    F.instantiatePrefix locals T
  expected-at (sp∷ checked rest) (suc i) = expected-at rest i

  abstract
    all2-append : ∀ {xs ys zs ws}
      → All2 _≈_ xs ys → All2 _≈_ zs ws → All2 _≈_ (xs ++ zs) (ys ++ ws)
    all2-append a2[] right = right
    all2-append (a2∷ equal rest) right = a2∷ equal (all2-append rest right)

    all2-reverse : ∀ {xs ys} → All2 _≈_ xs ys → All2 _≈_ (reverse xs) (reverse ys)
    all2-reverse a2[] = a2[]
    all2-reverse (a2∷ {x} {y} {xs} {ys} equal rest) =
      subst (λ zs → All2 _≈_ zs (reverse (y ∷ ys))) (sym (unfold-reverse x xs))
        (subst (All2 _≈_ (reverse xs ++ x ∷ [])) (sym (unfold-reverse y ys))
          (all2-append (all2-reverse rest) (a2∷ equal a2[])))

    spine-at : ∀ {n} {Γ : Ctx n} {locals args tele x′}
      → (source : Spine Γ locals args tele) → (i : Fin (len args))
      → _⇝_ sig (lookupAt args i) x′
      → Γ ⊢ x′ ⇐ expected-at source i
      → Spine Γ locals (setAt args i x′) tele × All2 _≈_ args (setAt args i x′)
    spine-at (sp∷ {locals = locals} {arg = arg} checked rest) zero step target =
      sp∷ target
        (S.spine-locals (a2∷ (rc step) (S.all2-refl locals)) rest) ,
      a2∷ (rc step) (S.all2-refl _)
    spine-at (sp∷ {arg = arg} checked rest) (suc i) step target
      with spine-at rest i step target
    ... | tail , equal = sp∷ checked tail , a2∷ (≈-refl {t = arg}) equal

    top-cong : ∀ {a a′} → a ≈ a′ → ∀ T → substTopT a T ≈ substTopT a′ T
    top-cong {a} {a′} equal T = ≈-subst-cong
      {t = T} {σ = topSub a} {σ′ = topSub a′}
      (λ { zero → equal ; (suc k) → ≈-refl {t = tm-var k} })

    app₁ : ∀ {n} {Γ : Ctx n} {f f′ a g d c}
      → _⇝_ sig f f′ → Γ ⊢ f ⇒ tm-pi g d c → Γ ⊢ f′ ⇒ tm-pi g d c
      → Γ ⊢ a ⇒ d → Γ ⊢ tm-app f′ a ⇒ substTopT a c
    app₁ step source target arg = ⇒-app target arg

    app₂ : ∀ {n} {Γ : Ctx n} {f a a′ g d c}
      → _⇝_ sig a a′ → Γ ⊢ f ⇒ tm-pi g d c
      → Γ ⊢ a ⇒ d → Γ ⊢ a′ ⇒ d
      → Γ ⊢ tm-app f a′ ⇒ substTopT a c
    app₂ {a = a} {a′} {c = c} step fun source target =
      ⇒-conv (⇒-app fun target)
        (≈-sym {t = substTopT a c} {u = substTopT a′ c} (top-cong (rc step) c))

    pi-dom : ∀ {n} {Γ : Ctx n} {g d d′ c i j}
      → WellFormed Γ → _⇝_ sig d d′
      → Γ ⊢ d ⇒ tm-type i → Γ ⊢ d′ ⇒ tm-type i
      → extend Γ d ⊢ c ⇒ tm-type j
      → Γ ⊢ tm-pi g d′ c ⇒ tm-type (i ⊔ˡ j)
    pi-dom wf step source target cod =
      ⇒-pi target (GV.context⇒ (GV.binder-context (rc step))
        (wf∷ wf (Sc.infer-scoped target) target) cod)

    pi-cod : ∀ {n} {Γ : Ctx n} {g d c c′ i j}
      → _⇝_ sig c c′ → Γ ⊢ d ⇒ tm-type i
      → extend Γ d ⊢ c ⇒ tm-type j → extend Γ d ⊢ c′ ⇒ tm-type j
      → Γ ⊢ tm-pi g d c′ ⇒ tm-type (i ⊔ˡ j)
    pi-cod step dom source target = ⇒-pi dom target

    lam-dom : ∀ {n} {Γ : Ctx n} {g d d′ b l c}
      → WellFormed Γ → _⇝_ sig d d′
      → Γ ⊢ d ⇒ tm-type l → Γ ⊢ d′ ⇒ tm-type l
      → extend Γ d ⊢ b ⇐ c → Γ ⊢ tm-lam g d′ b ⇒ tm-pi g d c
    lam-dom {g = g} {d} {d′} {c = c} wf step source target body =
      ⇒-conv
        (⇒-lam target (GV.context⇐ (GV.binder-context (rc step))
          (wf∷ wf (Sc.infer-scoped target) target) body))
        (≈-pi {g = g} {d = d′} {d′ = d} {c = c} {c′ = c}
          (≈-sym (rc step)) (≈-refl {t = c}))

    lam-body : ∀ {n} {Γ : Ctx n} {g d b b′ l c}
      → _⇝_ sig b b′ → Γ ⊢ d ⇒ tm-type l
      → extend Γ d ⊢ b ⇐ c → extend Γ d ⊢ b′ ⇐ c
      → Γ ⊢ tm-lam g d b′ ⇒ tm-pi g d c
    lam-body step dom source target = ⇒-lam dom target

    let-ty : ∀ {n} {Γ : Ctx n} {g ty ty′ v b l T}
      → WellFormed Γ → _⇝_ sig ty ty′
      → Γ ⊢ ty ⇒ tm-type l → Γ ⊢ ty′ ⇒ tm-type l
      → Γ ⊢ v ⇐ ty → extend Γ ty ⊢ b ⇒ T
      → Γ ⊢ tm-let g ty′ v b ⇒ substTopT v T
    let-ty wf step source target value body =
      ⇒-let target (⇐-conv value (rc step))
        (GV.context⇒ (GV.binder-context (rc step))
          (wf∷ wf (Sc.infer-scoped target) target) body)

    let-val : ∀ {n} {Γ : Ctx n} {g ty v v′ b l T}
      → _⇝_ sig v v′ → Γ ⊢ ty ⇒ tm-type l
      → Γ ⊢ v ⇐ ty → Γ ⊢ v′ ⇐ ty → extend Γ ty ⊢ b ⇒ T
      → Γ ⊢ tm-let g ty v′ b ⇒ substTopT v T
    let-val {v = v} {v′} {T = T} step kind source target body =
      ⇒-conv (⇒-let kind target body)
        (≈-sym {t = substTopT v T} {u = substTopT v′ T} (top-cong (rc step) T))

    let-body : ∀ {n} {Γ : Ctx n} {g ty v b b′ l T}
      → _⇝_ sig b b′ → Γ ⊢ ty ⇒ tm-type l → Γ ⊢ v ⇐ ty
      → extend Γ ty ⊢ b ⇒ T → extend Γ ty ⊢ b′ ⇒ T
      → Γ ⊢ tm-let g ty v b′ ⇒ substTopT v T
    let-body step kind value source target = ⇒-let kind value target

    effect-type : ∀ {n} {Γ : Ctx n} {t t′ l}
      → _⇝_ sig t t′ → Γ ⊢ t ⇒ tm-type l → Γ ⊢ t′ ⇒ tm-type l
      → Γ ⊢ tm-effect_type t′ ⇒ tm-type l
    effect-type step source target = ⇒-effect_type target

    effect-pure : ∀ {n} {Γ : Ctx n} {t t′ A}
      → _⇝_ sig t t′ → Γ ⊢ t ⇒ A → Γ ⊢ t′ ⇒ A
      → Γ ⊢ tm-effect_pure t′ ⇒ tm-effect_type A
    effect-pure step source target = ⇒-effect_pure target

    effect-bind₁ : ∀ {n} {Γ : Ctx n} {e e′ k A B}
      → _⇝_ sig e e′ → Γ ⊢ e ⇒ tm-effect_type A → Γ ⊢ e′ ⇒ tm-effect_type A
      → Γ ⊢ k ⇒ tm-pi unrestricted A (tm-effect_type (rename wk B))
      → Γ ⊢ tm-effect_bind e′ k ⇒ tm-effect_type B
    effect-bind₁ step source target kont = ⇒-effect_bind target kont

    effect-bind₂ : ∀ {n} {Γ : Ctx n} {e k k′ A B}
      → _⇝_ sig k k′ → Γ ⊢ e ⇒ tm-effect_type A
      → Γ ⊢ k ⇒ tm-pi unrestricted A (tm-effect_type (rename wk B))
      → Γ ⊢ k′ ⇒ tm-pi unrestricted A (tm-effect_type (rename wk B))
      → Γ ⊢ tm-effect_bind e k′ ⇒ tm-effect_type B
    effect-bind₂ step effect source target = ⇒-effect_bind effect target

    ctor-at : ∀ {n} {Γ : Ctx n} {name args A x′}
      → (view : I.ConstructorView Γ name args A)
      → (i : Fin (len args)) → _⇝_ sig (lookupAt args i) x′
      → Γ ⊢ x′ ⇐ expected-at (I.ConstructorView.fields-checked view) i
      → Γ ⊢ tm-ctor name (setAt args i x′) ⇒ A
    ctor-at {args = args} {A = A} {x′} view i step target
      with spine-at (I.ConstructorView.fields-checked view) i step target
    ... | fields , equal = ⇒-conv
      (⇒-ctor (I.ConstructorView.found view) (I.ConstructorView.parameters-checked view) fields)
      (≈-trans
        {t = tm-data (fam-name (I.ConstructorView.family view)) (I.ConstructorView.parameters view)
          (F.instantiateResults (I.ConstructorView.parameters view) (setAt args i x′)
            (ctor-indices (I.ConstructorView.ctor view)))}
        {u = tm-data (fam-name (I.ConstructorView.family view)) (I.ConstructorView.parameters view)
          (F.instantiateResults (I.ConstructorView.parameters view) args
            (ctor-indices (I.ConstructorView.ctor view)))}
        {v = A}
        (≈-data (S.all2-refl (I.ConstructorView.parameters view))
          (S.instantiateResults-cong (S.all2-refl (I.ConstructorView.parameters view))
            (all2-sym equal) (ctor-indices (I.ConstructorView.ctor view))))
        (I.ConstructorView.result-conversion view))
      where
        all2-sym : ∀ {xs ys} → All2 _≈_ xs ys → All2 _≈_ ys xs
        all2-sym a2[] = a2[]
        all2-sym (a2∷ equal rest) = a2∷ (≈-sym equal) (all2-sym rest)

    data-params-at : ∀ {n} {Γ : Ctx n} {name ps is family x′}
      → findFamily name (IndEnv.families ind) ≡ just family
      → (pars : Spine Γ [] ps (fam-params family))
      → Spine Γ (reverse ps) is (fam-indices family)
      → (i : Fin (len ps)) → _⇝_ sig (lookupAt ps i) x′
      → Γ ⊢ x′ ⇐ expected-at pars i
      → Γ ⊢ tm-data name (setAt ps i x′) is ⇒ tm-type (fam-level family)
    data-params-at found pars indices i step target with spine-at pars i step target
    ... | pars′ , equal =
      ⇒-data found pars′ (S.spine-locals (all2-reverse equal) indices)

    data-indices-at : ∀ {n} {Γ : Ctx n} {name ps is family x′}
      → findFamily name (IndEnv.families ind) ≡ just family
      → Spine Γ [] ps (fam-params family)
      → (indices : Spine Γ (reverse ps) is (fam-indices family))
      → (i : Fin (len is)) → _⇝_ sig (lookupAt is i) x′
      → Γ ⊢ x′ ⇐ expected-at indices i
      → Γ ⊢ tm-data name ps (setAt is i x′) ⇒ tm-type (fam-level family)
    data-indices-at found pars indices i step target =
      ⇒-data found pars (proj₁ (spine-at indices i step target))

  -- Common local premises of the native case rule, with no child-step
  -- or endpoint preservation assumption hidden inside the frame.
  record CaseFrame {n} (Γ : Ctx n) (name : Name) (ps is : List Term)
    (family : Family) (m : Term) (l : Core.Universe.Level) (brs : List Branch) : Set where
    field
      wf : WellFormed Γ
      found : findFamily name (IndEnv.families ind) ≡ just family
      parameters : Spine Γ [] ps (fam-params family)
      indices : Spine Γ (reverse ps) is (fam-indices family)
      motive-typed : Motive Γ family ps m l
      branches : Branches Γ family ps m brs
      covered : CaseCoverage ind name brs

  abstract
    case-scrutinee : ∀ {n} {Γ : Ctx n} {name ps is family m l brs s s′}
      → CaseFrame Γ name ps is family m l brs
      → _⇝_ sig s s′ → Γ ⊢ s ⇒ tm-data name ps is → Γ ⊢ s′ ⇒ tm-data name ps is
      → Γ ⊢ tm-case s′ m brs ⇒ Native.apps m (is ++ s ∷ [])
    case-scrutinee {is = is} {m = m} {s = s} {s′} frame step source target =
      ⇒-conv
        (⇒-case (CaseFrame.wf frame) (CaseFrame.found frame) target
          (CaseFrame.parameters frame) (CaseFrame.indices frame)
          (CaseFrame.motive-typed frame) (CaseFrame.branches frame) (CaseFrame.covered frame))
        (≈-sym
          {t = Native.apps m (is ++ s ∷ [])} {u = Native.apps m (is ++ s′ ∷ [])}
          (S.apps-cong (≈-refl {t = m})
            (all2-append (S.all2-refl is) (a2∷ (rc step) a2[]))))

    case-motive : ∀ {n} {Γ : Ctx n} {name ps is family m m′ l brs s}
      → CaseFrame Γ name ps is family m l brs
      → _⇝_ sig m m′ → Γ ⊢ s ⇒ tm-data name ps is
      → Γ ⊢ m′ ⇒ Native.motiveType family ps l
      → Γ ⊢ tm-case s m′ brs ⇒ Native.apps m (is ++ s ∷ [])
    case-motive {is = is} {family} {m} {m′} {brs = brs} {s} frame step scrutinee target
      with CaseFrame.motive-typed frame
    ... | motive scoped kind source =
      ⇒-conv
        (⇒-case (CaseFrame.wf frame) (CaseFrame.found frame) scrutinee
          (CaseFrame.parameters frame) (CaseFrame.indices frame)
          (motive (Sc.infer-scoped target) kind target)
          (S.branches-motive (rc step) (CaseFrame.branches frame)) (CaseFrame.covered frame))
        (≈-sym
          {t = Native.apps m (is ++ s ∷ [])} {u = Native.apps m′ (is ++ s ∷ [])}
          (S.apps-cong (rc step) (S.all2-refl (is ++ s ∷ []))))

    case-branches : ∀ {n} {Γ : Ctx n} {name ps is family m l brs brs′ s}
      → CaseFrame Γ name ps is family m l brs
      → _⇝*ᵇ_ sig brs brs′ → Γ ⊢ s ⇒ tm-data name ps is
      → Branches Γ family ps m brs′
      → Γ ⊢ tm-case s m brs′ ⇒ Native.apps m (is ++ s ∷ [])
    case-branches frame steps scrutinee target =
      ⇒-case (CaseFrame.wf frame) (CaseFrame.found frame) scrutinee
        (CaseFrame.parameters frame) (CaseFrame.indices frame)
        (CaseFrame.motive-typed frame) target
        (case-coverage-reduce sig steps (CaseFrame.covered frame))
