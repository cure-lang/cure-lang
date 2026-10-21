{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- An INHABITED instance of the CURRENT closed-entry soundness calculus.
-- Nat/Bounded here are the unindexed fragment required by BuiltinCtors,
-- not a claim that executable dependent signatures are already covered.
-- Full formal reduction compatibility is supplied, not postulated.
------------------------------------------------------------------------
module Proof.SoundnessModel where

open import Data.Bool using (true)
open import Data.Nat using (z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Data.Fin as Fin
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0)
open import Core.Syntax
open import Core.Signature
open import Core.Coverage
open import Core.Reduction
open import Core.Typing using (Conversion; Ctx; ⟨⟩; _∈Tele_; ∈-here; ∈-there)
open import Core.ClosedFragment using (ClosedFragmentSig)
open import Proof.Progress
open import Proof.Preservation using (ReduceConv; CertifiedTyped; module Preserve)
open import Proof.Soundness using (module Sound)
import Proof.ReductionConversion as Reduction
import Proof.CoverageExamples as Cases

N B : Term
N = tm-data "Nat" [] []
B = tm-data "Bounded" [] []

declared-N : Term
declared-N = tm-let unrestricted (tm-type l0) N (tm-var 0)

first next : Ctor
first = record { ctor-name = "First" ; ctor-args = ("_" , N) ∷ []
               ; ctor-params = [] ; ctor-indices = [] }
next = record { ctor-name = "Next" ; ctor-args = ("_" , N) ∷ ("_" , B) ∷ []
              ; ctor-params = [] ; ctor-indices = [] }

bounded-family : Family
bounded-family = record
  { fam-name = "Bounded" ; fam-params = [] ; fam-indices = [] ; fam-level = l0
  ; fam-ctors = first ∷ next ∷ [] ; positive = true ; universe-ok = true }

builtin : Name → Maybe Name
builtin "nat" = just "Nat"
builtin "bounded" = just "Bounded"
builtin _ = nothing

env : IndEnv
env = record { families = Cases.nat-family ∷ bounded-family ∷ [] ; builtins = builtin }

global-body global-type : Name → Maybe Term
global-body f with f ≟ "seven"
... | yes equal = just (tm-nat_lit 7)
... | no different = nothing
global-type f with f ≟ "seven"
... | yes equal = just declared-N
... | no different = nothing

sig : Signature
sig = record { body = global-body ; type-of = global-type }

closed-body : ∀ {f b} → Signature.body sig f ≡ just b → Scoped 0 b
closed-body {f} found with f ≟ "seven"
... | yes equal = subst (Scoped 0) (just-inj found) sc-nat_lit
... | no different = ⊥-elim (nothing≠just found)

module R = Reduction.Model sig (λ {f} {b} p → closed-body {f} {b} p)

conv : Conversion
conv = R.conversion

rc : ReduceConv sig conv
rc = R.reduce-converts

open Core.Typing.Typing env sig conv

positive-env : StrictlyPositive env
positive-env f (here refl) = refl
positive-env f (there (here refl)) = refl
positive-env f (there (there ()))

bodies-final : Certified sig
bodies-final {f} found with f ≟ "seven"
... | yes equal = subst Final (just-inj found) f-nat_lit
... | no different = ⊥-elim (nothing≠just found)

builtin-ctors : BuiltinCtors env
builtin-ctors =
  here refl , there (here refl) , there (there (here refl)) ,
  there (there (there (here refl))) , ("Nat" , refl) , ("Bounded" , refl) ,
  (λ { refl → refl }) , (λ { refl refl → refl }) ,
  (λ { refl refl → refl }) , (λ { refl refl refl → refl })

global-closed : ∀ f {T} → Signature.type-of sig f ≡ just T → Scoped 0 T
global-closed f found with f ≟ "seven"
... | yes equal = subst (Scoped 0) (just-inj found)
  (sc-let sc-type (sc-data st[] st[]) (sc-var (s≤s z≤n)))
... | no different = ⊥-elim (nothing≠just found)

params-closed : ∀ f → f ∈ IndEnv.families env → ∀ {T} → T ∈Tele fam-params f → Scoped 0 T
params-closed f (here refl) ()
params-closed f (there (here refl)) ()
params-closed f (there (there ())) entry

indices-closed : ∀ f → f ∈ IndEnv.families env → ∀ {T} → T ∈Tele fam-indices f → Scoped 0 T
indices-closed f (here refl) ()
indices-closed f (there (here refl)) ()
indices-closed f (there (there ())) entry

args-closed : ∀ f → f ∈ IndEnv.families env → ∀ ct → ct ∈ fam-ctors f
  → ∀ {T} → T ∈Tele ctor-args ct → Scoped 0 T
args-closed f (here refl) ct (here refl) ()
args-closed f (here refl) ct (there (here refl)) ∈-here = sc-data st[] st[]
args-closed f (here refl) ct (there (here refl)) (∈-there ())
args-closed f (here refl) ct (there (there ())) entry
args-closed f (there (here refl)) ct (here refl) ∈-here = sc-data st[] st[]
args-closed f (there (here refl)) ct (here refl) (∈-there ())
args-closed f (there (here refl)) ct (there (here refl)) ∈-here = sc-data st[] st[]
args-closed f (there (here refl)) ct (there (here refl)) (∈-there ∈-here) = sc-data st[] st[]
args-closed f (there (here refl)) ct (there (here refl)) (∈-there (∈-there ()))
args-closed f (there (here refl)) ct (there (there ())) entry
args-closed f (there (there ())) ct member entry

result-closed : ∀ f → f ∈ IndEnv.families env → ∀ ct → ct ∈ fam-ctors f
  → Scoped 0 (tm-data (fam-name f) (ctor-params ct) (ctor-indices ct))
result-closed f (here refl) ct (here refl) = sc-data st[] st[]
result-closed f (here refl) ct (there (here refl)) = sc-data st[] st[]
result-closed f (here refl) ct (there (there ()))
result-closed f (there (here refl)) ct (here refl) = sc-data st[] st[]
result-closed f (there (here refl)) ct (there (here refl)) = sc-data st[] st[]
result-closed f (there (here refl)) ct (there (there ()))
result-closed f (there (there ())) ct member

closed-signature : ClosedFragmentSig env sig
closed-signature = global-closed , params-closed , indices-closed , args-closed , result-closed

typed-bodies : CertifiedTyped env sig conv
typed-bodies {f} body-found type-found with f ≟ "seven"
... | yes equal with just-inj body-found | just-inj type-found
... | refl | refl = sc-nat_lit , ⇒-conv (⇒-nat_lit refl)
  (Conversion.≈-sym conv {t = declared-N} {u = N} (rc {t = declared-N} {t′ = N} ζ))
typed-bodies {f} body-found type-found | no different = ⊥-elim (nothing≠just body-found)

module P = Preserve env sig conv closed-signature rc typed-bodies builtin-ctors bodies-final
module S = Sound env sig conv positive-env bodies-final builtin-ctors closed-signature rc typed-bodies

eq-refl : ∀ {t} → Conversion._≈_ conv t t
eq-refl {t} = Conversion.≈-refl conv {t}

nat-kind : ∀ {k} {Γ : Ctx k} → Γ ⊢ N ⇒ tm-type l0
nat-kind = ⇒-data refl ⊢*[] ⊢*[]

declared-N-kind : ∀ {k} {Γ : Ctx k} → Γ ⊢ declared-N ⇒ tm-type l0
declared-N-kind =
  ⇒-let (⇒-type refl) (⇐-infer nat-kind (eq-refl {tm-type l0})) (⇒-var Fin.zero)

identity : Term
identity = tm-lam unrestricted N (tm-var 0)

identity-typed : ⟨⟩ ⊢ identity ⇒ tm-pi unrestricted N N
identity-typed = ⇒-lam nat-kind (⇐-infer (⇒-var Fin.zero) (eq-refl {N}))

beta-program : Term
beta-program = tm-app identity (tm-nat_lit 7)

beta-typed : ⟨⟩ ⊢ beta-program ⇒ N
beta-typed = ⇒-app identity-typed (⇒-nat_lit refl)

beta-final : Final beta-program
beta-final = f-app (f-lam (f-data ft[] ft[]) f-var) f-nat_lit

beta-preserved : ⟨⟩ ⊢ tm-nat_lit 7 ⇒ N
beta-preserved = P.preservation⇒ beta-final beta-typed β

zeta-program : Term
zeta-program = tm-let unrestricted N (tm-nat_lit 7) (tm-var 0)

zeta-typed : ⟨⟩ ⊢ zeta-program ⇒ N
zeta-typed = ⇒-let nat-kind (⇐-infer (⇒-nat_lit refl) (eq-refl {N})) (⇒-var Fin.zero)

zeta-preserved : ⟨⟩ ⊢ tm-nat_lit 7 ⇒ N
zeta-preserved = P.preservation⇒
  (f-let (f-data ft[] ft[]) f-nat_lit f-var) zeta-typed ζ

motive : Term
motive = tm-lam unrestricted N N

motive-typed : ⟨⟩ ⊢ motive ⇒ tm-pi unrestricted N (tm-type l0)
motive-typed = ⇒-lam nat-kind (⇐-infer nat-kind (eq-refl {tm-type l0}))

motive-contracts : ∀ a → Conversion._≈_ conv (tm-app motive a) N
motive-contracts a = rc {t = tm-app motive a} {t′ = N} β

motive-goal : ∀ a → Conversion._≈_ conv N (tm-app motive a)
motive-goal a = Conversion.≈-sym conv {t = tm-app motive a} {u = N} (motive-contracts a)

branches : List Branch
branches = ("Z" , 0 , tm-nat_lit 7) ∷ ("S" , 1 , tm-var 0) ∷ []

branches-typed : ⟨⟩ ⊢*brs branches ⇐*ᵇ ("Nat" , motive)
branches-typed =
  brs∷ refl (⇐-infer (⇒-nat_lit refl) (motive-goal (tm-ctor "Z" [])))
    (brs∷ refl (⇐-infer (⇒-var Fin.zero) (motive-goal (tm-ctor "S" (tm-var 0 ∷ [])))) brs[])

constructors-covered : ∀ {c f ct}
  → findCtor c (IndEnv.families env) ≡ just (f , ct) → fam-name f ≡ "Nat"
  → HasBranch c (length (ctor-args ct)) branches
constructors-covered {c} {f} {ct} found owner
  with lookup-ctor-members {c = c} {fs = IndEnv.families env} {f = f} {ct = ct} found
... | here refl , here refl , refl = tm-nat_lit 7 , refl
... | here refl , there (here refl) , refl = tm-var 0 , refl
... | here refl , there (there ()) , name
constructors-covered found () | there (here refl) , member , name
constructors-covered found owner | there (there ()) , member , name

covered : CaseCoverage env "Nat" branches
covered = record
  { ctor-covered = constructors-covered
  ; nat-zero-covered = λ _ → tm-nat_lit 7 , refl
  ; nat-suc-covered = λ _ → tm-var 0 , refl
  ; bounded-zero-covered = λ ()
  ; bounded-suc-covered = λ () }

case-program : Term
case-program = tm-case (tm-nat_lit 0) motive branches

case-typed : ⟨⟩ ⊢ case-program ⇒ N
case-typed = ⇒-conv (⇒-case (⇒-nat_lit refl) motive-typed branches-typed covered)
  (motive-contracts (tm-nat_lit 0))

case-final : Final case-program
case-final = f-case f-nat_lit (f-lam (f-data ft[] ft[]) (f-data ft[] ft[]))
  (fb∷ f-nat_lit (fb∷ f-var fb[]))

iota-preserved : ⟨⟩ ⊢ tm-nat_lit 7 ⇒ N
iota-preserved = P.preservation⇒ case-final case-typed (ι-nat-zero refl refl)

ctor-case-program : Term
ctor-case-program = tm-case (tm-ctor "Z" []) motive branches

ctor-case-typed : ⟨⟩ ⊢ ctor-case-program ⇒ N
ctor-case-typed = ⇒-conv
  (⇒-case (⇒-ctor refl ⊢*[]) motive-typed branches-typed covered)
  (motive-contracts (tm-ctor "Z" []))

ordinary-iota-preserved : ⟨⟩ ⊢ tm-nat_lit 7 ⇒ N
ordinary-iota-preserved = P.preservation⇒
  (f-case (f-ctor ft[]) (f-lam (f-data ft[] ft[]) (f-data ft[] ft[]))
    (fb∷ f-nat_lit (fb∷ f-var fb[])))
  ctor-case-typed (ι refl refl)

successor-case-typed : ⟨⟩ ⊢ tm-case (tm-nat_lit 8) motive branches ⇒ N
successor-case-typed = ⇒-conv
  (⇒-case (⇒-nat_lit refl) motive-typed branches-typed covered)
  (motive-contracts (tm-nat_lit 8))

successor-iota-preserved : ⟨⟩ ⊢ tm-nat_lit 7 ⇒ N
successor-iota-preserved = P.preservation⇒
  (f-case f-nat_lit (f-lam (f-data ft[] ft[]) (f-data ft[] ft[]))
    (fb∷ f-nat_lit (fb∷ f-var fb[])))
  successor-case-typed (ι-nat-suc refl refl)

global-typed : ⟨⟩ ⊢ tm-global "seven" ⇒ N
global-typed = ⇒-conv (⇒-global refl) (rc {t = declared-N} {t′ = N} ζ)

delta-preserved : ⟨⟩ ⊢ tm-nat_lit 7 ⇒ N
delta-preserved = P.preservation⇒ f-global global-typed (δ refl)

-- Actual invocation of the existing constructive soundness theorem.
case-soundness : S.FuelResult case-program N
case-soundness = S.soundness-fuel 2 (⇐-infer case-typed (eq-refl {N})) case-final
