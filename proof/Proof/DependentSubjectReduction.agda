------------------------------------------------------------------------
-- Recursive native preservation, not a collection of endpoint premises.
-- Every recursive child typing is derived from the original evidence.
-- Literal layouts and global body FINALITY are explicit; neither is a
-- semantic termination theorem or executable NbE/refinement claim.
------------------------------------------------------------------------
module Proof.DependentSubjectReduction where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Syntax
open import Core.Signature
open import Core.Typing using (Ctx; ⟨⟩; extend; Conversion; All2; a2[]; a2∷)
open import Core.Reduction
open import Core.Coverage using (CaseCoverage)
import Core.DependentTyping as Native
import Core.LocalFrame as F
open import Proof.Progress
  using (BodiesFinal; Final; FinalTerms; FinalBranches;
         f-type; f-var; f-pi; f-lam; f-app; f-let; f-data; f-ctor; f-case; f-global;
         f-int_type; f-int_lit; f-float_type; f-float_lit; f-atom_type; f-atom_lit;
         f-binary_type; f-nat_lit; f-bounded_lit; f-effect_type; f-effect_pure; f-effect_bind;
         ft[]; ft∷; fb[]; fb∷)
import Proof.FinalPreservation as Finality
import Proof.DependentCoherence as Coherence
import Proof.DependentGeneralTransport as General
import Proof.DependentTypingInversion as Inversion
import Proof.DependentCongruence as Congruence
import Proof.DependentGeneralIota as Iota
open import Proof.DependentDataConversion using (DataComponents)
import Proof.DependentLiteralPreservation as Literals
open import Proof.Substitution using (rename-closed)

module Preserve (ind : IndEnv) (sig : Signature) (conv : Conversion)
  (valid : Native.Typing.SignatureValid ind sig conv)
  (components : DataComponents conv)
  (rc : ∀ {t u} → _⇝_ sig t u → Conversion._≈_ conv t u)
  (bodies-final : BodiesFinal sig) (shapes : Literals.BuiltinShapes ind) where
  open Native.Typing ind sig conv
  open Conversion conv
  module G = General.General ind sig conv
  module V = G.Valid valid
  module C = Congruence.Laws ind sig conv valid rc
  module I = Inversion.Laws ind sig conv
  module K = Coherence.NativeFrames ind sig conv
  module GI = Iota.Preservation ind sig conv valid components
  module L = Literals.Laws ind sig conv valid components rc shapes

  infer-reduct : ∀ {n} {Γ : Ctx n} {t u T}
    → Final t → _⇝_ sig t u → Γ ⊢ u ⇐ T → Γ ⊢ u ⇒ T
  infer-reduct final step checked =
    K.check-infer (Finality.final-preservation sig bodies-final final step) checked

  case-frame : ∀ {n} {Γ : Ctx n} {name ps is family mot l brs}
    → WellFormed Γ → findFamily name (IndEnv.families ind) ≡ just family
    → Spine Γ [] ps (fam-params family) → Spine Γ (reverse ps) is (fam-indices family)
    → Motive Γ family ps mot l → Branches Γ family ps mot brs → CaseCoverage ind name brs
    → C.CaseFrame Γ name ps is family mot l brs
  case-frame wf found params indices mot branches covered = record
    { wf = wf ; found = found ; parameters = params ; indices = indices
    ; motive-typed = mot ; branches = branches ; covered = covered }

  constructor-case : ∀ {n} {Γ : Ctx n} {name fields family-name ps is family mot l brs}
    → C.CaseFrame Γ family-name ps is family mot l brs
    → Γ ⊢ tm-ctor name fields ⇒ tm-data family-name ps is
    → GI.SourceCase Γ name fields mot brs
  constructor-case frame typed = record
    { family-name = _ ; family = _ ; parameters = _ ; indices = _
    ; found-family = C.CaseFrame.found frame ; caller = C.CaseFrame.wf frame
    ; scrutinee = typed ; parameters-checked = C.CaseFrame.parameters frame
    ; indices-checked = C.CaseFrame.indices frame ; level = _
    ; motive-valid = C.CaseFrame.motive-typed frame ; branches = C.CaseFrame.branches frame
    ; coverage = C.CaseFrame.covered frame }

  beta-root : ∀ {n} {Γ : Ctx n} {g d b a g′ d′ c}
    → WellFormed Γ → Γ ⊢ tm-lam g d b ⇒ tm-pi g′ d′ c → Γ ⊢ a ⇒ d′
    → Γ ⊢ substTopT a b ⇐ substTopT a c
  beta-root {g = g} {d = d} {a = a} {g′ = g′} {d′ = d′} {c = c} wf fun arg
    with I.lambda-inference fun
  ... | local-cod , body , between
    with ≈-pi-components {g = g′} {d = d′} {c = c}
      {g′ = g} {d′ = d} {c′ = local-cod} between
  ... | grade , domain , codomain =
    ⇐-conv (V.subst⇐ (V.top-coherent (⇒-conv arg (≈-sym domain))) wf body)
      (≈-subst (topSub a) codomain)

  delta-root : ∀ {n} {Γ : Ctx n} {name body T}
    → WellFormed Γ → Signature.type-of sig name ≡ just T → Signature.body sig name ≡ just body
    → Γ ⊢ body ⇐ T
  delta-root {T = T} wf declared found with SignatureValid.global-body valid found
  ... | T′ , declared′ , scoped , typed with just-inj (trans (sym declared′) declared)
  ... | refl = ⇐-infer
    (G.cast⇒ (rename-closed scoped)
      (rename-closed (proj₁ (SignatureValid.global-type valid declared)))
      (V.rename⇒ {ρ = λ i → i}
        (record { index = λ () ; agrees = λ () ; types = λ () }) wf typed))
    ≈-refl

  mutual
    preservation⇒ : ∀ {n} {Γ : Ctx n} {t u T}
      → WellFormed Γ → Γ ⊢ t ⇒ T → Final t → _⇝_ sig t u → Γ ⊢ u ⇐ T
    preservation⇒ wf (⇒-type level) final ()
    preservation⇒ wf (⇒-var i) final ()
    preservation⇒ wf (⇒-global declared) f-global (δ found) = delta-root wf declared found
    preservation⇒ wf ⇒-int_type final ()
    preservation⇒ wf ⇒-float_type final ()
    preservation⇒ wf ⇒-binary_type final ()
    preservation⇒ wf ⇒-atom_type final ()
    preservation⇒ wf ⇒-int_lit final ()
    preservation⇒ wf ⇒-float_lit final ()
    preservation⇒ wf ⇒-atom_lit final ()
    preservation⇒ wf (⇒-nat_lit builtin found ps is) final ()
    preservation⇒ wf (⇒-bounded_lit builtin found ps is) final ()
    preservation⇒ wf (⇒-conv typed equal) final step =
      ⇐-conv (preservation⇒ wf typed final step) equal
    preservation⇒ wf (⇒-cumul typed le) final step =
      ⇐-cumul (infer-reduct final step (preservation⇒ wf typed final step)) le
    preservation⇒ wf (⇒-app fun arg) (f-app ff fa) β = beta-root wf fun arg
    preservation⇒ wf (⇒-app fun arg) (f-app ff fa) (ξ-app₁ step) =
      ⇐-infer (C.app₁ step fun (infer-reduct ff step (preservation⇒ wf fun ff step)) arg) ≈-refl
    preservation⇒ wf (⇒-app fun arg) (f-app ff fa) (ξ-app₂ step) =
      ⇐-infer (C.app₂ step fun arg (infer-reduct fa step (preservation⇒ wf arg fa step))) ≈-refl
    preservation⇒ wf (⇒-let kind value body) (f-let ft fv fb) ζ =
      ⇐-infer (V.subst⇒ (V.top-coherent (K.check-infer fv value)) wf body) ≈-refl
    preservation⇒ wf (⇒-let kind value body) (f-let ft fv fb) (ξ-let step) =
      ⇐-infer (C.let-val step kind value (preservation⇐ wf value fv step) body) ≈-refl
    preservation⇒ wf (⇒-let kind value body) (f-let ft fv fb) (ξ-let-ty step) =
      ⇐-infer (C.let-ty wf step kind (infer-reduct ft step (preservation⇒ wf kind ft step)) value body) ≈-refl
    preservation⇒ wf (⇒-let kind value body) (f-let ft fv fb) (ξ-let-body step) =
      ⇐-infer (C.let-body step kind value body
        (infer-reduct fb step (preservation⇒ (wf∷ wf (G.Sc.infer-scoped kind) kind) body fb step))) ≈-refl
    preservation⇒ wf (⇒-pi dom cod) (f-pi fd fc) (ξ-pi-dom step) =
      ⇐-infer (C.pi-dom wf step dom (infer-reduct fd step (preservation⇒ wf dom fd step)) cod) ≈-refl
    preservation⇒ wf (⇒-pi dom cod) (f-pi fd fc) (ξ-pi-cod step) =
      ⇐-infer (C.pi-cod step dom cod
        (infer-reduct fc step (preservation⇒ (wf∷ wf (G.Sc.infer-scoped dom) dom) cod fc step))) ≈-refl
    preservation⇒ wf (⇒-lam dom body) (f-lam fd fb) (ξ-lam-dom step) =
      ⇐-infer (C.lam-dom wf step dom (infer-reduct fd step (preservation⇒ wf dom fd step)) body) ≈-refl
    preservation⇒ wf (⇒-lam dom body) (f-lam fd fb) (ξ-lam-body step) =
      ⇐-infer (C.lam-body step dom body
        (preservation⇐ (wf∷ wf (G.Sc.infer-scoped dom) dom) body fb step)) ≈-refl
    preservation⇒ wf (⇒-data found params indices) (f-data fp fi) (ξ-data-params-at i step) =
      ⇐-infer (C.data-params-at found params indices i step (preservation-at wf params fp i step)) ≈-refl
    preservation⇒ wf (⇒-data found params indices) (f-data fp fi) (ξ-data-indices-at i step) =
      ⇐-infer (C.data-indices-at found params indices i step (preservation-at wf indices fi i step)) ≈-refl
    preservation⇒ wf (⇒-ctor {ps = ps} {family = family} {ctor = ctor} found params fields)
      (f-ctor final) (ξ-ctor-at i step) =
      ⇐-infer (C.ctor-at
        (record { family = family ; ctor = ctor ; parameters = ps ; found = found
                ; parameters-checked = params ; fields-checked = fields ; result-conversion = ≈-refl })
        i step (preservation-at wf fields final i step)) ≈-refl
    preservation⇒ wf (⇒-effect_type typed) (f-effect_type final) (ξ-effect_type step) =
      ⇐-infer (C.effect-type step typed (infer-reduct final step (preservation⇒ wf typed final step))) ≈-refl
    preservation⇒ wf (⇒-effect_pure typed) (f-effect_pure final) (ξ-effect_pure step) =
      ⇐-infer (C.effect-pure step typed (infer-reduct final step (preservation⇒ wf typed final step))) ≈-refl
    preservation⇒ wf (⇒-effect_bind effect cont) (f-effect_bind fe fk) (ξ-effect_bind₁ step) =
      ⇐-infer (C.effect-bind₁ step effect (infer-reduct fe step (preservation⇒ wf effect fe step)) cont) ≈-refl
    preservation⇒ wf (⇒-effect_bind effect cont) (f-effect_bind fe fk) (ξ-effect_bind₂ step) =
      ⇐-infer (C.effect-bind₂ step effect cont (infer-reduct fk step (preservation⇒ wf cont fk step))) ≈-refl
    preservation⇒ wf (⇒-case wf₀ found scrutinee params indices mot branches covered)
      (f-case (f-ctor finals) fm fbs) (ι selected arity) =
      proj₂ (proj₂ (GI.preserve-at
        (constructor-case (case-frame wf₀ found params indices mot branches covered) scrutinee)
        finals selected ≈-refl))
    preservation⇒ wf (⇒-case wf₀ found scrutinee params indices mot branches covered)
      (f-case fs fm fbs) (ι-nat-zero selected arity) =
      L.nat-zero (case-frame wf₀ found params indices mot branches covered) scrutinee selected arity
    preservation⇒ wf (⇒-case wf₀ found scrutinee params indices mot branches covered)
      (f-case fs fm fbs) (ι-nat-suc selected arity) =
      L.nat-suc (case-frame wf₀ found params indices mot branches covered) scrutinee selected arity
    preservation⇒ wf (⇒-case wf₀ found scrutinee params indices mot branches covered)
      (f-case fs fm fbs) (ι-bounded-zero selected arity) =
      L.bounded-zero (case-frame wf₀ found params indices mot branches covered) scrutinee selected arity
    preservation⇒ wf (⇒-case wf₀ found scrutinee params indices mot branches covered)
      (f-case fs fm fbs) (ι-bounded-suc selected arity) =
      L.bounded-suc (case-frame wf₀ found params indices mot branches covered) scrutinee selected arity
    preservation⇒ wf (⇒-case wf₀ found scrutinee params indices mot branches covered)
      (f-case fs fm fbs) (ξ-case step) =
      ⇐-infer (C.case-scrutinee (case-frame wf₀ found params indices mot branches covered) step scrutinee
        (infer-reduct fs step (preservation⇒ wf scrutinee fs step))) ≈-refl
    preservation⇒ wf (⇒-case wf₀ found scrutinee params indices mot branches covered)
      (f-case fs fm fbs) (ξ-case-motive step) =
      ⇐-infer (C.case-motive (case-frame wf₀ found params indices mot branches covered) step scrutinee
        (preservation-motive wf mot fm step)) ≈-refl
    preservation⇒ wf (⇒-case wf₀ found scrutinee params indices mot branches covered)
      (f-case fs fm fbs) (ξ-case-brs steps) =
      ⇐-infer (C.case-branches (case-frame wf₀ found params indices mot branches covered) steps scrutinee
        (preservation-branches branches fbs steps)) ≈-refl

    preservation⇐ : ∀ {n} {Γ : Ctx n} {t u T}
      → WellFormed Γ → Γ ⊢ t ⇐ T → Final t → _⇝_ sig t u → Γ ⊢ u ⇐ T
    preservation⇐ wf ⇐-hole () step
    preservation⇐ wf (⇐-infer typed equal) final step =
      ⇐-conv (preservation⇒ wf typed final step) equal
    preservation⇐ wf (⇐-conv typed equal) final step =
      ⇐-conv (preservation⇐ wf typed final step) equal
    preservation⇐ wf (⇐-cumul typed le) final step =
      ⇐-cumul (infer-reduct final step (preservation⇒ wf typed final step)) le
    preservation⇐ wf (⇐-lam dom body) (f-lam fd fb) (ξ-lam-dom step) =
      ⇐-infer (C.lam-dom wf step dom (infer-reduct fd step (preservation⇒ wf dom fd step)) body) ≈-refl
    preservation⇐ wf (⇐-lam dom body) (f-lam fd fb) (ξ-lam-body step) =
      ⇐-lam dom (preservation⇐ (wf∷ wf (G.Sc.infer-scoped dom) dom) body fb step)

    preservation-at : ∀ {n} {Γ : Ctx n} {locals args tele x′}
      → WellFormed Γ → (spine : Spine Γ locals args tele) → FinalTerms args
      → (i : Fin (len args)) → _⇝_ sig (lookupAt args i) x′
      → Γ ⊢ x′ ⇐ C.expected-at spine i
    preservation-at wf sp[] ft[] () step
    preservation-at wf (sp∷ checked rest) (ft∷ final finals) zero step =
      preservation⇐ wf checked final step
    preservation-at wf (sp∷ checked rest) (ft∷ final finals) (suc i) step =
      preservation-at wf rest finals i step

    preservation-motive : ∀ {n} {Γ : Ctx n} {family ps mot mot′ l}
      → WellFormed Γ → Motive Γ family ps mot l → Final mot → _⇝_ sig mot mot′
      → Γ ⊢ mot′ ⇒ Native.motiveType family ps l
    preservation-motive wf (motive scope kind typed) final step =
      infer-reduct final step (preservation⇒ wf typed final step)

    preservation-branches : ∀ {n} {Γ : Ctx n} {family ps mot brs brs′}
      → Branches Γ family ps mot brs → FinalBranches brs → _⇝*ᵇ_ sig brs brs′
      → Branches Γ family ps mot brs′
    preservation-branches br[] fb[] ⇝ᵇ-nil = br[]
    preservation-branches (br∷ found owner opening wf body rest) (fb∷ final finals)
      (⇝ᵇ-cons path tail) =
      br∷ found owner opening wf (preservation-star⇐ wf body final path)
        (preservation-branches rest finals tail)

    preservation-star⇐ : ∀ {n} {Γ : Ctx n} {t u T}
      → WellFormed Γ → Γ ⊢ t ⇐ T → Final t → _⇝*_ sig t u → Γ ⊢ u ⇐ T
    preservation-star⇐ wf typed final ⇝*-refl = typed
    preservation-star⇐ wf typed final (⇝*-step step rest) =
      preservation-star⇐ wf (preservation⇐ wf typed final step)
        (Finality.final-preservation sig bodies-final final step) rest

  preservation-infers : ∀ {n} {Γ : Ctx n} {t u T}
    → WellFormed Γ → Γ ⊢ t ⇒ T → Final t → _⇝_ sig t u → Γ ⊢ u ⇒ T
  preservation-infers wf typed final step =
    infer-reduct final step (preservation⇒ wf typed final step)
