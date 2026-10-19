------------------------------------------------------------------------
-- Total representation expansion of compact Nat/Bounded literals.
-- No beta/zeta/iota/delta evaluation, value collapse, or erasure occurs.
-- This is a formal-calculus construction, not executable NbE refinement.
------------------------------------------------------------------------
module Core.LiteralExpansion where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Core.Syntax
open import Core.TypeHeads
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Core.Reduction using (Signature; findBranch; argsSub; argsSub-go; substArgs)
open import Core.Signature using (just-inj)

nat : ℕ → Term
nat zero = tm-ctor "Z" []
nat (suc n) = tm-ctor "S" (nat n ∷ [])

bounded : ℕ → Term
bounded zero = tm-ctor "First" (nat 0 ∷ [])
bounded (suc n) = tm-ctor "Next" (nat n ∷ bounded n ∷ [])

nat-rename : ∀ ρ n → rename ρ (nat n) ≡ nat n
nat-rename ρ zero = refl
nat-rename ρ (suc n) = cong (λ x → tm-ctor "S" (x ∷ [])) (nat-rename ρ n)

bounded-rename : ∀ ρ n → rename ρ (bounded n) ≡ bounded n
bounded-rename ρ zero = refl
bounded-rename ρ (suc n) = cong₂ (λ x y → tm-ctor "Next" (x ∷ y ∷ [])) (nat-rename ρ n) (bounded-rename ρ n)

nat-subst : ∀ σ n → substS σ (nat n) ≡ nat n
nat-subst σ zero = refl
nat-subst σ (suc n) = cong (λ x → tm-ctor "S" (x ∷ [])) (nat-subst σ n)

bounded-subst : ∀ σ n → substS σ (bounded n) ≡ bounded n
bounded-subst σ zero = refl
bounded-subst σ (suc n) = cong₂ (λ x y → tm-ctor "Next" (x ∷ y ∷ [])) (nat-subst σ n) (bounded-subst σ n)

mutual
  expand : Term → Term
  expand (tm-type l) = tm-type l
  expand (tm-var k) = tm-var k
  expand (tm-pi g d c) = tm-pi g (expand d) (expand c)
  expand (tm-lam g d b) = tm-lam g (expand d) (expand b)
  expand (tm-let g ty v b) = tm-let g (expand ty) (expand v) (expand b)
  expand (tm-app f a) = tm-app (expand f) (expand a)
  expand (tm-data n ps is) = tm-data n (expandTerms ps) (expandTerms is)
  expand (tm-ctor n args) = tm-ctor n (expandTerms args)
  expand (tm-case s m brs) =
    tm-case (expand s) (expand m) (expandBranches brs)
  expand (tm-global n) = tm-global n
  expand tm-int_type = tm-int_type
  expand (tm-int_lit k) = tm-int_lit k
  expand (tm-nat_lit k) = nat k
  expand (tm-bounded_lit k) = bounded k
  expand tm-float_type = tm-float_type
  expand tm-float_lit = tm-float_lit
  expand tm-binary_type = tm-binary_type
  expand tm-atom_type = tm-atom_type
  expand (tm-atom_lit n) = tm-atom_lit n
  expand (tm-effect_type a) = tm-effect_type (expand a)
  expand (tm-effect_pure a) = tm-effect_pure (expand a)
  expand (tm-effect_bind e k) = tm-effect_bind (expand e) (expand k)
  expand (tm-hole n) = tm-hole n
  expand tm-absurd = tm-absurd

  expandTerms : List Term → List Term
  expandTerms [] = []
  expandTerms (x ∷ xs) = expand x ∷ expandTerms xs

  expandBranch : Branch → Branch
  expandBranch (cn , ar , b) = cn , ar , expand b

  expandBranches : List Branch → List Branch
  expandBranches [] = []
  expandBranches (x ∷ xs) = expandBranch x ∷ expandBranches xs

mutual
  expand-rename : ∀ ρ t → expand (rename ρ t) ≡ rename ρ (expand t)
  expand-rename ρ (tm-type l) = refl
  expand-rename ρ (tm-var k) = refl
  expand-rename ρ (tm-pi g d c) =
    cong₂ (tm-pi g) (expand-rename ρ d) (expand-rename (ext ρ) c)
  expand-rename ρ (tm-lam g d b) =
    cong₂ (tm-lam g) (expand-rename ρ d) (expand-rename (ext ρ) b)
  expand-rename ρ (tm-let g ty v b) =
    cong₃ (tm-let g) (expand-rename ρ ty) (expand-rename ρ v) (expand-rename (ext ρ) b)
  expand-rename ρ (tm-app f a) =
    cong₂ tm-app (expand-rename ρ f) (expand-rename ρ a)
  expand-rename ρ (tm-data n ps is) =
    cong₂ (tm-data n) (expand-rename-terms ρ ps) (expand-rename-terms ρ is)
  expand-rename ρ (tm-ctor n args) = cong (tm-ctor n) (expand-rename-terms ρ args)
  expand-rename ρ (tm-case s m brs) =
    cong₃ tm-case (expand-rename ρ s) (expand-rename ρ m)
                 (expand-rename-branches ρ brs)
  expand-rename ρ (tm-global n) = refl
  expand-rename ρ tm-int_type = refl
  expand-rename ρ (tm-int_lit k) = refl
  expand-rename ρ (tm-nat_lit k) = sym (nat-rename ρ k)
  expand-rename ρ (tm-bounded_lit k) = sym (bounded-rename ρ k)
  expand-rename ρ tm-float_type = refl
  expand-rename ρ tm-float_lit = refl
  expand-rename ρ tm-binary_type = refl
  expand-rename ρ tm-atom_type = refl
  expand-rename ρ (tm-atom_lit n) = refl
  expand-rename ρ (tm-effect_type a) = cong tm-effect_type (expand-rename ρ a)
  expand-rename ρ (tm-effect_pure a) = cong tm-effect_pure (expand-rename ρ a)
  expand-rename ρ (tm-effect_bind e k) =
    cong₂ tm-effect_bind (expand-rename ρ e) (expand-rename ρ k)
  expand-rename ρ (tm-hole n) = refl
  expand-rename ρ tm-absurd = refl

  expand-rename-terms : ∀ ρ ts
    → expandTerms (renameTerms ρ ts) ≡ renameTerms ρ (expandTerms ts)
  expand-rename-terms ρ [] = refl
  expand-rename-terms ρ (x ∷ xs) =
    cong₂ _∷_ (expand-rename ρ x) (expand-rename-terms ρ xs)

  expand-rename-branch : ∀ ρ br
    → expandBranch (renameBranch ρ br) ≡ renameBranch ρ (expandBranch br)
  expand-rename-branch ρ (cn , ar , b) =
    cong (λ x → cn , ar , x) (expand-rename (ext^ ar ρ) b)

  expand-rename-branches : ∀ ρ brs
    → expandBranches (renameBranches ρ brs) ≡ renameBranches ρ (expandBranches brs)
  expand-rename-branches ρ [] = refl
  expand-rename-branches ρ (x ∷ xs) =
    cong₂ _∷_ (expand-rename-branch ρ x) (expand-rename-branches ρ xs)

expandSub : Sub → Sub
expandSub σ k = expand (σ k)

expand-ext : ∀ ar σ k
  → expandSub (extSub^ ar σ) k ≡ extSub^ ar (expandSub σ) k
expand-ext zero σ k = refl
expand-ext (suc ar) σ zero = refl
expand-ext (suc ar) σ (suc k) =
  trans (expand-rename wk (extSub^ ar σ k))
        (cong (rename wk) (expand-ext ar σ k))

mutual
  expand-subst : ∀ σ t → expand (substS σ t) ≡ substS (expandSub σ) (expand t)
  expand-subst σ (tm-type l) = refl
  expand-subst σ (tm-var k) = refl
  expand-subst σ (tm-pi g d c) =
    cong₂ (tm-pi g) (expand-subst σ d) (expand-subst-binders 1 σ c)
  expand-subst σ (tm-lam g d b) =
    cong₂ (tm-lam g) (expand-subst σ d) (expand-subst-binders 1 σ b)
  expand-subst σ (tm-let g ty v b) =
    cong₃ (tm-let g) (expand-subst σ ty) (expand-subst σ v) (expand-subst-binders 1 σ b)
  expand-subst σ (tm-app f a) =
    cong₂ tm-app (expand-subst σ f) (expand-subst σ a)
  expand-subst σ (tm-data n ps is) =
    cong₂ (tm-data n) (expand-subst-terms σ ps) (expand-subst-terms σ is)
  expand-subst σ (tm-ctor n args) = cong (tm-ctor n) (expand-subst-terms σ args)
  expand-subst σ (tm-case s m brs) =
    cong₃ tm-case (expand-subst σ s) (expand-subst σ m)
                 (expand-subst-branches σ brs)
  expand-subst σ (tm-global n) = refl
  expand-subst σ tm-int_type = refl
  expand-subst σ (tm-int_lit k) = refl
  expand-subst σ (tm-nat_lit k) = sym (nat-subst (expandSub σ) k)
  expand-subst σ (tm-bounded_lit k) = sym (bounded-subst (expandSub σ) k)
  expand-subst σ tm-float_type = refl
  expand-subst σ tm-float_lit = refl
  expand-subst σ tm-binary_type = refl
  expand-subst σ tm-atom_type = refl
  expand-subst σ (tm-atom_lit n) = refl
  expand-subst σ (tm-effect_type a) = cong tm-effect_type (expand-subst σ a)
  expand-subst σ (tm-effect_pure a) = cong tm-effect_pure (expand-subst σ a)
  expand-subst σ (tm-effect_bind e k) =
    cong₂ tm-effect_bind (expand-subst σ e) (expand-subst σ k)
  expand-subst σ (tm-hole n) = refl
  expand-subst σ tm-absurd = refl

  expand-subst-binders : ∀ ar σ t
    → expand (substS (extSub^ ar σ) t) ≡ substS (extSub^ ar (expandSub σ)) (expand t)
  expand-subst-binders ar σ t =
    trans (expand-subst (extSub^ ar σ) t)
          (cong (λ τ → substS τ (expand t)) (funext (expand-ext ar σ)))

  expand-subst-terms : ∀ σ ts
    → expandTerms (substTermsS σ ts) ≡ substTermsS (expandSub σ) (expandTerms ts)
  expand-subst-terms σ [] = refl
  expand-subst-terms σ (x ∷ xs) =
    cong₂ _∷_ (expand-subst σ x) (expand-subst-terms σ xs)

  expand-subst-branch : ∀ σ br
    → expandBranch (substBranchS σ br) ≡ substBranchS (expandSub σ) (expandBranch br)
  expand-subst-branch σ (cn , ar , b) =
    cong (λ x → cn , ar , x) (expand-subst-binders ar σ b)

  expand-subst-branches : ∀ σ brs
    → expandBranches (substBranchesS σ brs) ≡ substBranchesS (expandSub σ) (expandBranches brs)
  expand-subst-branches σ [] = refl
  expand-subst-branches σ (x ∷ xs) =
    cong₂ _∷_ (expand-subst-branch σ x) (expand-subst-branches σ xs)

nat-scoped : ∀ d n → Scoped d (nat n)
nat-scoped d zero = sc-ctor st[]
nat-scoped d (suc n) = sc-ctor (st∷ (nat-scoped d n) st[])

bounded-scoped : ∀ d n → Scoped d (bounded n)
bounded-scoped d zero = sc-ctor (st∷ (nat-scoped d 0) st[])
bounded-scoped d (suc n) = sc-ctor (st∷ (nat-scoped d n) (st∷ (bounded-scoped d n) st[]))

mutual
  expand-scoped : ∀ {d t} → Scoped d t → Scoped d (expand t)
  expand-scoped sc-type = sc-type
  expand-scoped (sc-var p) = sc-var p
  expand-scoped (sc-pi p q) = sc-pi (expand-scoped p) (expand-scoped q)
  expand-scoped (sc-lam p q) = sc-lam (expand-scoped p) (expand-scoped q)
  expand-scoped (sc-let p q r) = sc-let (expand-scoped p) (expand-scoped q) (expand-scoped r)
  expand-scoped (sc-app p q) = sc-app (expand-scoped p) (expand-scoped q)
  expand-scoped (sc-data p q) = sc-data (expand-scoped-terms p) (expand-scoped-terms q)
  expand-scoped (sc-ctor p) = sc-ctor (expand-scoped-terms p)
  expand-scoped (sc-case p q r) = sc-case (expand-scoped p) (expand-scoped q) (expand-scoped-branches r)
  expand-scoped sc-global = sc-global
  expand-scoped sc-int_type = sc-int_type
  expand-scoped sc-int_lit = sc-int_lit
  expand-scoped {d} {tm-nat_lit n} sc-nat_lit = nat-scoped d n
  expand-scoped {d} {tm-bounded_lit n} sc-bounded_lit = bounded-scoped d n
  expand-scoped sc-float_type = sc-float_type
  expand-scoped sc-float_lit = sc-float_lit
  expand-scoped sc-binary_type = sc-binary_type
  expand-scoped sc-atom_type = sc-atom_type
  expand-scoped sc-atom_lit = sc-atom_lit
  expand-scoped (sc-effect_type p) = sc-effect_type (expand-scoped p)
  expand-scoped (sc-effect_pure p) = sc-effect_pure (expand-scoped p)
  expand-scoped (sc-effect_bind p q) = sc-effect_bind (expand-scoped p) (expand-scoped q)
  expand-scoped sc-hole = sc-hole
  expand-scoped sc-absurd = sc-absurd

  expand-scoped-terms : ∀ {d xs} → ScopedTerms d xs → ScopedTerms d (expandTerms xs)
  expand-scoped-terms st[] = st[]
  expand-scoped-terms (st∷ p ps) = st∷ (expand-scoped p) (expand-scoped-terms ps)

  expand-scoped-branches : ∀ {d bs} → ScopedBranches d bs → ScopedBranches d (expandBranches bs)
  expand-scoped-branches sb[] = sb[]
  expand-scoped-branches (sb∷ (sbranch p) ps) =
    sb∷ (sbranch (expand-scoped p)) (expand-scoped-branches ps)

expandMaybe : Maybe Term → Maybe Term
expandMaybe nothing = nothing
expandMaybe (just t) = just (expand t)

expandSig : Signature → Signature
expandSig sig = record
  { body = λ f → expandMaybe (Signature.body sig f)
  ; type-of = λ f → expandMaybe (Signature.type-of sig f) }

expanded-body-closed : ∀ sig
  → (∀ {f b} → Signature.body sig f ≡ just b → Scoped 0 b)
  → ∀ {f b} → Signature.body (expandSig sig) f ≡ just b → Scoped 0 b
expanded-body-closed sig closed {f} eq with Signature.body sig f in found
... | nothing with eq
... | ()
expanded-body-closed sig closed {f} eq | just b =
  subst (Scoped 0) (just-inj eq) (expand-scoped (closed found))

expand-head : ∀ {t h} → HasTypeHead t h → HasTypeHead (expand t) h
expand-head ty-universe = ty-universe
expand-head ty-pi = ty-pi
expand-head ty-data = ty-data
expand-head ty-int = ty-int
expand-head ty-float = ty-float
expand-head ty-binary = ty-binary
expand-head ty-atom = ty-atom
expand-head ty-effect = ty-effect

expand-length : ∀ xs → Data.List.length (expandTerms xs) ≡ Data.List.length xs
expand-length [] = refl
expand-length (x ∷ xs) = cong suc (expand-length xs)

expand-lookup : ∀ c bs {ar b} → findBranch c bs ≡ just (c , ar , b)
  → findBranch c (expandBranches bs) ≡ just (c , ar , expand b)
expand-lookup c [] ()
expand-lookup c ((cn , ar , b) ∷ bs) found with c ≟ cn
... | yes refl =
  cong (λ q → just (c , Data.Product.proj₁ (Data.Product.proj₂ q) ,
    expand (Data.Product.proj₂ (Data.Product.proj₂ q)))) (just-inj found)
... | no different = expand-lookup c bs found

expand-top : ∀ a b → expand (substTopT a b) ≡ substTopT (expand a) (expand b)
expand-top a b =
  trans (expand-subst (topSub a) b)
    (cong (λ σ → substS σ (expand b)) (funext (λ { zero → refl ; (suc k) → refl })))

expand-argsSub : ∀ n xs k → expand (argsSub-go n xs k) ≡ argsSub-go n (expandTerms xs) k
expand-argsSub n [] k = refl
expand-argsSub n (x ∷ xs) zero = refl
expand-argsSub n (x ∷ xs) (suc k) = expand-argsSub (suc n) xs k

expand-args : ∀ xs b → expand (substArgs xs b) ≡ substArgs (expandTerms xs) (expand b)
expand-args xs b =
  trans (expand-subst (argsSub xs) b)
    (cong (λ σ → substS σ (expand b)) (funext (expand-argsSub 0 xs)))

