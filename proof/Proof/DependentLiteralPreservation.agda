------------------------------------------------------------------------
-- Native compact literal peeling. Static shapes mention actual lookups;
-- they contain no typing or preservation callback.
------------------------------------------------------------------------
module Proof.DependentLiteralPreservation where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
open import Core.Signature
open import Core.TypeHeads
open import Core.Typing using (Ctx; Conversion; All2; a2[]; a2∷)
open import Core.Reduction
import Core.DependentTyping as Native
import Core.LocalFrame as F
import Proof.DependentCongruence as Congruence
import Proof.DependentGeneralIota as General
import Proof.DependentSpineConversion as Spine
open import Proof.DependentDataConversion using (DataComponents)
open import Proof.Progress using (FinalTerms; ft[]; ft∷; f-nat_lit; f-bounded_lit)

record ConstructorShape (ind : IndEnv) (family : Family)
  (name : Name) (args : Telescope) : Set where
  field
    ctor : Ctor
    found : findCtor name (IndEnv.families ind) ≡ just (family , ctor)
    fields : ctor-args ctor ≡ args
    results : ctor-indices ctor ≡ []

record NatShape (ind : IndEnv) (name : Name) (family : Family) : Set where
  field
    predecessor : Name
    zero-shape : ConstructorShape ind family "Z" []
    suc-shape : ConstructorShape ind family "S" ((predecessor , tm-data name [] []) ∷ [])

record BoundedShape (ind : IndEnv) (name : Name) (family : Family) : Set where
  field
    nat-name : Name
    nat-family : Family
    nat-builtin : IndEnv.builtins ind "nat" ≡ just nat-name
    nat-found : findFamily nat-name (IndEnv.families ind) ≡ just nat-family
    nat-parameters : fam-params nat-family ≡ []
    nat-indices : fam-indices nat-family ≡ []
    bound first-bound predecessor : Name
    zero-shape : ConstructorShape ind family "First"
      ((first-bound , tm-data nat-name [] []) ∷ [])
    suc-shape : ConstructorShape ind family "Next"
      ((bound , tm-data nat-name [] []) ∷ (predecessor , tm-data name [] []) ∷ [])

record BuiltinShapes (ind : IndEnv) : Set where
  field
    nat-shape : ∀ {name family}
      → IndEnv.builtins ind "nat" ≡ just name
      → findFamily name (IndEnv.families ind) ≡ just family
      → fam-params family ≡ [] → fam-indices family ≡ []
      → NatShape ind name family
    bounded-shape : ∀ {name family}
      → IndEnv.builtins ind "bounded" ≡ just name
      → findFamily name (IndEnv.families ind) ≡ just family
      → fam-params family ≡ [] → fam-indices family ≡ []
      → BoundedShape ind name family

-- In particular, no-builtin environments need not contain Nat or Bounded.
no-builtins : ∀ ind → (∀ key → IndEnv.builtins ind key ≡ nothing) → BuiltinShapes ind
no-builtins ind absent = record
  { nat-shape = λ identity → ⊥-elim (nothing≠just (trans (sym (absent "nat")) identity))
  ; bounded-shape = λ identity → ⊥-elim (nothing≠just (trans (sym (absent "bounded")) identity)) }

data Kind : Set where
  nat bounded : Kind

key : Kind → Name
key nat = "nat"
key bounded = "bounded"

literal : Kind → ℕ → Term
literal nat = tm-nat_lit
literal bounded = tm-bounded_lit

family-name : ∀ {name fs family} → findFamily name fs ≡ just family → name ≡ fam-name family
family-name {fs = []} ()
family-name {name} {f ∷ fs} found with name ≟ fam-name f
... | yes refl = cong fam-name (just-inj found)
... | no different = family-name {fs = fs} found

module Laws (ind : IndEnv) (sig : Signature) (conv : Conversion)
  (valid : Native.Typing.SignatureValid ind sig conv)
  (components : DataComponents conv)
  (rc : ∀ {t u} → _⇝_ sig t u → Conversion._≈_ conv t u)
  (shapes : BuiltinShapes ind) where
  open Native.Typing ind sig conv
  open Conversion conv
  module C = Congruence.Laws ind sig conv valid rc
  module P = General.Preservation ind sig conv valid components
  module S = Spine.Laws ind sig conv
  open C using (CaseFrame)

  record LiteralView (kind : Kind) (A : Term) : Set where
    field
      name : Name
      family : Family
      builtin : IndEnv.builtins ind (key kind) ≡ just name
      found : findFamily name (IndEnv.families ind) ≡ just family
      parameters : fam-params family ≡ []
      indices : fam-indices family ≡ []
      equal : tm-data name [] [] ≈ A

  data-not-sort : ∀ {name ps is l} → tm-data name ps is ≈ tm-type l → Data.Empty.⊥
  data-not-sort equal with ≈-heads ty-data ty-universe equal
  ... | ()
  convert-view : ∀ {kind A B} → LiteralView kind A → A ≈ B → LiteralView kind B
  convert-view view equal = record
    { name = LiteralView.name view ; family = LiteralView.family view
    ; builtin = LiteralView.builtin view ; found = LiteralView.found view
    ; parameters = LiteralView.parameters view ; indices = LiteralView.indices view
    ; equal = ≈-trans (LiteralView.equal view) equal }

  infer-literal : ∀ kind {n} {Γ : Ctx n} {k A}
    → Γ ⊢ literal kind k ⇒ A → LiteralView kind A
  infer-literal nat (⇒-nat_lit {name = name} {family} builtin found pars inds) =
    record { name = name ; family = family ; builtin = builtin ; found = found
           ; parameters = pars ; indices = inds ; equal = ≈-refl }
  infer-literal bounded (⇒-bounded_lit {name = name} {family} builtin found pars inds) =
    record { name = name ; family = family ; builtin = builtin ; found = found
           ; parameters = pars ; indices = inds ; equal = ≈-refl }
  infer-literal kind {A = A} (⇒-conv {T = B} der equal) with infer-literal kind der
  ... | view = convert-view {A = B} {B = A} view equal
  infer-literal kind (⇒-cumul der le) =
    ⊥-elim (data-not-sort (LiteralView.equal (infer-literal kind der)))

  check-literal : ∀ kind {n} {Γ : Ctx n} {k A}
    → Γ ⊢ literal kind k ⇐ A → LiteralView kind A
  check-literal nat {A = A} (⇐-infer {T′ = B} der equal) with infer-literal nat der
  ... | view = convert-view {A = B} {B = A} view equal
  check-literal bounded {A = A} (⇐-infer {T′ = B} der equal) with infer-literal bounded der
  ... | view = convert-view {A = B} {B = A} view equal
  check-literal nat {A = A} (⇐-conv {T = B} der equal) with check-literal nat der
  ... | view = convert-view {A = B} {B = A} view equal
  check-literal bounded {A = A} (⇐-conv {T = B} der equal) with check-literal bounded der
  ... | view = convert-view {A = B} {B = A} view equal
  check-literal nat (⇐-cumul der le) =
    ⊥-elim (data-not-sort (LiteralView.equal (infer-literal nat der)))
  check-literal bounded (⇐-cumul der le) =
    ⊥-elim (data-not-sort (LiteralView.equal (infer-literal bounded der)))

  record DataView (kind : Kind) (name : Name) (ps is : List Term) : Set where
    field
      family : Family
      builtin : IndEnv.builtins ind (key kind) ≡ just name
      found : findFamily name (IndEnv.families ind) ≡ just family
      parameters : fam-params family ≡ []
      indices : fam-indices family ≡ []
      no-parameters : ps ≡ []
      no-indices : is ≡ []

  data-literal : ∀ kind {n} {Γ : Ctx n} {k name ps is}
    → Γ ⊢ literal kind k ⇒ tm-data name ps is → DataView kind name ps is
  data-literal kind der with infer-literal kind der
  ... | view with DataComponents.components components (LiteralView.equal view)
  ... | refl , a2[] , a2[] = record
    { family = LiteralView.family view ; builtin = LiteralView.builtin view
    ; found = LiteralView.found view ; parameters = LiteralView.parameters view
    ; indices = LiteralView.indices view ; no-parameters = refl ; no-indices = refl }

  constructor-typed : ∀ {n} {Γ : Ctx n} {name family c tele args}
    → findFamily name (IndEnv.families ind) ≡ just family
    → fam-params family ≡ []
    → ConstructorShape ind family c tele
    → Spine Γ [] args tele → Γ ⊢ tm-ctor c args ⇒ tm-data name [] []
  constructor-typed {Γ = Γ} {name = name} {family} {c} {args = args} found pars shape fields =
    subst (λ name → Γ ⊢ tm-ctor c args ⇒ tm-data name [] [])
      (sym (family-name {name} {IndEnv.families ind} {family} found))
      (⇒-conv (⇒-ctor (ConstructorShape.found shape)
        (subst (Spine Γ [] []) (sym pars) sp[])
        (subst (Spine Γ [] args) (sym (ConstructorShape.fields shape)) fields))
        (subst (λ results → tm-data (fam-name family) [] (F.instantiateResults [] args results)
          ≈ tm-data (fam-name family) [] [])
          (sym (ConstructorShape.results shape)) ≈-refl))

  contract : ∀ {n} {Γ : Ctx n} {name ps is family mot level brs c args original ar b}
    → CaseFrame Γ name ps is family mot level brs
    → Γ ⊢ tm-ctor c args ⇒ tm-data name ps is
    → FinalTerms args → tm-ctor c args ≈ original
    → findBranch c brs ≡ just (c , ar , b)
    → Γ ⊢ substArgs args b ⇐ Native.apps mot (is ++ original ∷ [])
  contract {is = is} {mot = mot} frame typed finals equal selected =
    proj₂ (proj₂ (P.preserve-at
      (record { family-name = _ ; family = _ ; parameters = _ ; indices = _
              ; found-family = C.CaseFrame.found frame ; caller = C.CaseFrame.wf frame
              ; scrutinee = typed ; parameters-checked = C.CaseFrame.parameters frame
              ; indices-checked = C.CaseFrame.indices frame ; level = _
              ; motive-valid = C.CaseFrame.motive-typed frame
              ; branches = C.CaseFrame.branches frame ; coverage = C.CaseFrame.covered frame })
      finals selected (S.apps-cong (≈-refl {t = mot})
        (P.all2-append (S.all2-refl is) (a2∷ equal a2[])))))

  nat-zero : ∀ {n} {Γ : Ctx n} {name ps is family mot level brs ar b}
    → CaseFrame Γ name ps is family mot level brs
    → Γ ⊢ tm-nat_lit 0 ⇒ tm-data name ps is
    → findBranch "Z" brs ≡ just ("Z" , ar , b) → 0 ≡ ar
    → Γ ⊢ substArgs [] b ⇐ Native.apps mot (is ++ tm-nat_lit 0 ∷ [])
  nat-zero frame typed selected arity with data-literal nat typed
  ... | view with DataView.no-parameters view | DataView.no-indices view
  ... | refl | refl = contract frame
    (constructor-typed (DataView.found view) (DataView.parameters view)
      (NatShape.zero-shape shape) sp[]) ft[] ≈-nat-zero selected
    where
      shape = BuiltinShapes.nat-shape shapes (DataView.builtin view)
        (DataView.found view) (DataView.parameters view) (DataView.indices view)

  nat-suc : ∀ {n} {Γ : Ctx n} {k name ps is family mot level brs ar b}
    → CaseFrame Γ name ps is family mot level brs
    → Γ ⊢ tm-nat_lit (suc k) ⇒ tm-data name ps is
    → findBranch "S" brs ≡ just ("S" , ar , b) → 1 ≡ ar
    → Γ ⊢ substArgs (tm-nat_lit k ∷ []) b
      ⇐ Native.apps mot (is ++ tm-nat_lit (suc k) ∷ [])
  nat-suc frame typed selected arity with data-literal nat typed
  ... | view with DataView.no-parameters view | DataView.no-indices view
  ... | refl | refl = contract frame
    (constructor-typed (DataView.found view) (DataView.parameters view)
      (NatShape.suc-shape shape)
      (sp∷ (⇐-infer (⇒-nat_lit (DataView.builtin view) (DataView.found view)
        (DataView.parameters view) (DataView.indices view)) ≈-refl) sp[]))
    (ft∷ f-nat_lit ft[]) ≈-nat-suc selected
    where
      shape = BuiltinShapes.nat-shape shapes (DataView.builtin view)
        (DataView.found view) (DataView.parameters view) (DataView.indices view)

  bounded-zero : ∀ {n} {Γ : Ctx n} {name ps is family mot level brs ar b}
    → CaseFrame Γ name ps is family mot level brs
    → Γ ⊢ tm-bounded_lit 0 ⇒ tm-data name ps is
    → findBranch "First" brs ≡ just ("First" , ar , b) → 1 ≡ ar
    → Γ ⊢ substArgs (tm-nat_lit 0 ∷ []) b
      ⇐ Native.apps mot (is ++ tm-bounded_lit 0 ∷ [])
  bounded-zero frame typed selected arity with data-literal bounded typed
  ... | view with DataView.no-parameters view | DataView.no-indices view
  ... | refl | refl = contract frame
    (constructor-typed (DataView.found view) (DataView.parameters view)
      (BoundedShape.zero-shape shape)
      (sp∷ (⇐-infer (⇒-nat_lit (BoundedShape.nat-builtin shape) (BoundedShape.nat-found shape)
        (BoundedShape.nat-parameters shape) (BoundedShape.nat-indices shape)) ≈-refl) sp[]))
    (ft∷ f-nat_lit ft[]) ≈-bounded-zero selected
    where
      shape = BuiltinShapes.bounded-shape shapes (DataView.builtin view)
        (DataView.found view) (DataView.parameters view) (DataView.indices view)

  bounded-suc : ∀ {n} {Γ : Ctx n} {k name ps is family mot level brs ar b}
    → CaseFrame Γ name ps is family mot level brs
    → Γ ⊢ tm-bounded_lit (suc k) ⇒ tm-data name ps is
    → findBranch "Next" brs ≡ just ("Next" , ar , b) → 2 ≡ ar
    → Γ ⊢ substArgs (tm-nat_lit k ∷ tm-bounded_lit k ∷ []) b
      ⇐ Native.apps mot (is ++ tm-bounded_lit (suc k) ∷ [])
  bounded-suc frame typed selected arity with data-literal bounded typed
  ... | view with DataView.no-parameters view | DataView.no-indices view
  ... | refl | refl = contract frame
    (constructor-typed (DataView.found view) (DataView.parameters view)
      (BoundedShape.suc-shape shape)
      (sp∷ (⇐-infer (⇒-nat_lit (BoundedShape.nat-builtin shape) (BoundedShape.nat-found shape)
        (BoundedShape.nat-parameters shape) (BoundedShape.nat-indices shape)) ≈-refl)
        (sp∷ (⇐-infer (⇒-bounded_lit (DataView.builtin view) (DataView.found view)
          (DataView.parameters view) (DataView.indices view)) ≈-refl) sp[])))
    (ft∷ f-nat_lit (ft∷ f-bounded_lit ft[])) ≈-bounded-suc selected
    where
      shape = BuiltinShapes.bounded-shape shapes (DataView.builtin view)
        (DataView.found view) (DataView.parameters view) (DataView.indices view)
