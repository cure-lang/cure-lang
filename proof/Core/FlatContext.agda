------------------------------------------------------------------------
-- A closure-free semantic value/context MODEL. No evaluator, function
-- eta, arbitrary Value representation or implementation refinement.
-- Out-of-scope levels fail; natural subtraction is never a fallback.
------------------------------------------------------------------------
module Core.FlatContext where

open import Data.Empty using (⊥)
import Data.Unit
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _∸_; s≤s)
import Data.Nat.Properties as Nat
import Data.Vec as V
import Data.Fin as Fin
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Core.Syntax using (Name; Term; tm-type; tm-atom_type; tm-atom_lit; tm-var;
  Scoped; sc-type; sc-atom_type; sc-atom_lit; sc-var; rename; wk)
open import Core.Grade using (Grade; unrestricted)
open import Core.Universe using (Level)
open import Core.Typing using (Ctx; ⟨⟩; _▷_; extend; renameCtx; lookup)
import Core.WireConversion as C
import Core.Signature

data Value : Set where
  sort : Level → Value
  atom-type : Value
  atom : Name → Value
  neutral : ℕ → Value

data Reads (depth : ℕ) : Value → Term → Set where
  q-sort : ∀ {l} → Reads depth (sort l) (tm-type l)
  q-atom-type : Reads depth atom-type tm-atom_type
  q-atom : ∀ {name} → Reads depth (atom name) (tm-atom_lit name)
  q-neutral : ∀ {level} → level < depth → Reads depth (neutral level) (tm-var (depth ∸ suc level))

reify : ℕ → Value → Maybe Term
reify depth (sort l) = just (tm-type l)
reify depth atom-type = just tm-atom_type
reify depth (atom name) = just (tm-atom_lit name)
reify depth (neutral level) with Nat._<?_ level depth
... | yes inside = just (tm-var (depth ∸ suc level))
... | no outside = nothing

quote-complete : ∀ {n v t} → Reads n v t → reify n v ≡ just t
quote-complete q-sort = refl
quote-complete q-atom-type = refl
quote-complete q-atom = refl
quote-complete {n} (q-neutral {level} inside) with Nat._<?_ level n
... | yes bounded = refl
... | no outside = Data.Empty.⊥-elim (outside inside)
quote-sound : ∀ n v t → reify n v ≡ just t → Reads n v t
quote-sound n (sort l) .(tm-type l) refl = q-sort
quote-sound n atom-type .tm-atom_type refl = q-atom-type
quote-sound n (atom name) .(tm-atom_lit name) refl = q-atom
quote-sound n (neutral level) t found with Nat._<?_ level n
... | no outside = Data.Empty.⊥-elim (Core.Signature.nothing≠just found)
... | yes inside with Core.Signature.just-inj found
... | refl = q-neutral inside

index-bounded : ∀ n level → level < n → (n ∸ suc level) < n
index-bounded zero level ()
index-bounded (suc n) level inside = s≤s (Nat.m∸n≤m n level)
scoped : ∀ {n v t} → Reads n v t → Scoped n t
scoped q-sort = sc-type
scoped q-atom-type = sc-atom_type
scoped q-atom = sc-atom_lit
scoped (q-neutral {level} inside) = sc-var (index-bounded _ level inside)
raise-index : ∀ n level → level < n
  → suc n ∸ suc level ≡ suc (n ∸ suc level)
raise-index zero level ()
raise-index (suc n) zero inside = refl
raise-index (suc n) (suc level) (s≤s inside) = raise-index n level inside
weaken : ∀ {n v t} → Reads n v t → Reads (suc n) v (rename wk t)
weaken q-sort = q-sort
weaken q-atom-type = q-atom-type
weaken q-atom = q-atom
weaken {n} (q-neutral {level} inside) = subst (λ k → Reads (suc n) (neutral level) (tm-var k))
  (raise-index n level inside) (q-neutral (Nat.<-trans inside (Nat.n<1+n n)))
fresh : ∀ n → Reads (suc n) (neutral n) (tm-var 0)
fresh n = subst (λ k → Reads (suc n) (neutral n) (tm-var k))
  (Nat.n∸n≡0 n) (q-neutral (Nat.n<1+n n))

data ReadValues (depth : ℕ) : ∀ {n} → Vec Value n → Vec Term n → Set where
  q[] : ReadValues depth [] []
  q∷ : ∀ {n v t} {vs : Vec Value n} {ts}
    → Reads depth v t → ReadValues depth vs ts → ReadValues depth (v ∷ vs) (t ∷ ts)
quote-values : ∀ {n} → ℕ → Vec Value n → Maybe (Vec Term n)
quote-values depth [] = just []
quote-values depth (v ∷ vs) = C.pair _∷_ (reify depth v) (quote-values depth vs)
values-complete : ∀ {d n} {vs : Vec Value n} {ts} → ReadValues d vs ts → quote-values d vs ≡ just ts
values-complete q[] = refl
values-complete (q∷ v vs) rewrite quote-complete v | values-complete vs = refl
weaken-values : ∀ {d n} {vs : Vec Value n} {ts} → ReadValues d vs ts
  → ReadValues (suc d) vs (V.map (rename wk) ts)
weaken-values q[] = q[]
weaken-values (q∷ v vs) = q∷ (weaken v) (weaken-values vs)

-- Signature is a fixed parameter; all operations preserve it. The actual
-- capture separately checks its source signature against the source audit.
record Store {S : Set} (signature : S) (size : ℕ) : Set where
  constructor store
  field
    types : Vec Value size
    grades : Vec Grade size
    environment : Vec Value size
open Store public
empty : ∀ {S : Set} (signature : S) → Store signature 0
empty signature = store [] [] []
extend-opaque : ∀ {S : Set} {signature : S} {n} → Store signature n → Value → Grade → Store signature (suc n)
extend-opaque {n = n} ctx ty grade = store (ty ∷ types ctx) (grade ∷ grades ctx) (neutral n ∷ environment ctx)
defined : ∀ {S : Set} {signature : S} {n} → Store signature n → Value → Value → Store signature (suc n)
defined ctx ty value = store (ty ∷ types ctx) (unrestricted ∷ grades ctx) (value ∷ environment ctx)

data Built {S : Set} {signature : S} : ∀ {n} → Store signature n → Ctx n → Set where
  b-empty : Built (empty signature) ⟨⟩
  b-opaque : ∀ {n} {ctx : Store signature n} {Γ ty T} → Built ctx Γ
    → Reads n ty T → (grade : Grade) → Built (extend-opaque ctx ty grade) (extend Γ T)
  b-defined : ∀ {n} {ctx : Store signature n} {Γ ty T value term} → Built ctx Γ
    → Reads n ty T → Reads n value term → Built (defined ctx ty value) (extend Γ T)

context-types : ∀ {n} → Ctx n → Vec Term n
context-types ⟨⟩ = []
context-types (Γ ▷ T) = T ∷ context-types Γ
weaken-types : ∀ {d n} (Γ : Ctx n) {vs} → ReadValues d vs (context-types Γ)
  → ReadValues (suc d) vs (context-types (renameCtx wk Γ))
weaken-types ⟨⟩ q[] = q[]
weaken-types (Γ ▷ T) (q∷ v vs) = q∷ (weaken v) (weaken-types Γ vs)
type-view : ∀ {S : Set} {signature : S} {n} {ctx : Store signature n} {Γ}
  → Built ctx Γ → ReadValues n (types ctx) (context-types Γ)
type-view b-empty = q[]
type-view (b-opaque {Γ = Γ} built ty grade) = q∷ (weaken ty) (weaken-types Γ (type-view built))
type-view (b-defined {Γ = Γ} built ty value) = q∷ (weaken ty) (weaken-types Γ (type-view built))
environment-terms : ∀ {S : Set} {signature : S} {n} {ctx : Store signature n} {Γ}
  → Built ctx Γ → Vec Term n
environment-terms b-empty = []
environment-terms (b-opaque built ty grade) = tm-var 0 ∷ V.map (rename wk) (environment-terms built)
environment-terms (b-defined {term = term} built ty value) =
  rename wk term ∷ V.map (rename wk) (environment-terms built)
environment-view : ∀ {S : Set} {signature : S} {n} {ctx : Store signature n} {Γ}
  → (built : Built ctx Γ) → ReadValues n (environment ctx) (environment-terms built)
environment-view b-empty = q[]
environment-view (b-opaque {n = n} built ty grade) = q∷ (fresh n) (weaken-values (environment-view built))
environment-view (b-defined built ty value) = q∷ (weaken value) (weaken-values (environment-view built))

identity-terms : ∀ n → Vec Term n
identity-terms zero = []
identity-terms (suc n) = tm-var 0 ∷ V.map (rename wk) (identity-terms n)
OpaqueOnly : ∀ {S : Set} {signature : S} {n} {ctx : Store signature n} {Γ} → Built ctx Γ → Set
OpaqueOnly b-empty = Data.Unit.⊤
OpaqueOnly (b-opaque built ty grade) = OpaqueOnly built
OpaqueOnly (b-defined built ty value) = ⊥
opaque-identity : ∀ {S : Set} {signature : S} {n} {ctx : Store signature n} {Γ}
  → (built : Built ctx Γ) → OpaqueOnly built → environment-terms built ≡ identity-terms n
opaque-identity b-empty opaque-only = refl
opaque-identity (b-opaque built ty grade) opaque-only =
  cong (tm-var 0 ∷_) (cong (V.map (rename wk)) (opaque-identity built opaque-only))
opaque-identity (b-defined built ty value) ()

read-lookup : ∀ {d n} {vs : Vec Value n} {ts} → ReadValues d vs ts
  → (i : Fin.Fin n) → Reads d (V.lookup vs i) (V.lookup ts i)
read-lookup (q∷ value values) Fin.zero = value
read-lookup (q∷ value values) (Fin.suc i) = read-lookup values i
native-lookup : ∀ {n} (Γ : Ctx n) (i : Fin.Fin n) → V.lookup (context-types Γ) i ≡ lookup Γ i
native-lookup (Γ ▷ T) Fin.zero = refl
native-lookup (Γ ▷ T) (Fin.suc i) = native-lookup Γ i
lookup-view : ∀ {S : Set} {signature : S} {n} {ctx : Store signature n} {Γ}
  → Built ctx Γ → (i : Fin.Fin n) → Reads n (V.lookup (types ctx) i) (lookup Γ i)
lookup-view {Γ = Γ} built i =
  subst (Reads _ _) (native-lookup Γ i) (read-lookup (type-view built) i)
map-lookup : ∀ {n} (f : Term → Term) (ts : Vec Term n) i
  → V.lookup (V.map f ts) i ≡ f (V.lookup ts i)
map-lookup f (t ∷ ts) Fin.zero = refl
map-lookup f (t ∷ ts) (Fin.suc i) = map-lookup f ts i
identity-lookup : ∀ n (i : Fin.Fin n) → V.lookup (identity-terms n) i ≡ tm-var (Fin.toℕ i)
identity-lookup (suc n) Fin.zero = refl
identity-lookup (suc n) (Fin.suc i) rewrite map-lookup (rename wk) (identity-terms n) i
  | identity-lookup n i = refl
