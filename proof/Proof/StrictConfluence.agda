------------------------------------------------------------------------
-- Strong diamond for genuinely one-step parallel reduction, then checked
-- closure confluence. Only registered global-body closedness is assumed;
-- there is no typing, conversion, coverage or termination oracle.
------------------------------------------------------------------------
module Proof.StrictConfluence where

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Core.Syntax
open import Core.Signature using (just-inj)
open import Core.Reduction
open import Core.Relation
open import Core.StrictParallel
open import Proof.Substitution
  using (rename-topSub; rename-substArgs; subst-topSub; subst-argsSub;
         rename-closed; substS-closed)

module Laws (sig : Signature)
  (closed : ∀ {f b} → Signature.body sig f ≡ just b → Scoped 0 b) where
  open Parallel sig public

  rename-length : ∀ ρ xs → length (renameTerms ρ xs) ≡ length xs
  rename-length ρ [] = refl
  rename-length ρ (x ∷ xs) = cong suc (rename-length ρ xs)

  subst-length : ∀ σ xs → length (substTermsS σ xs) ≡ length xs
  subst-length σ [] = refl
  subst-length σ (x ∷ xs) = cong suc (subst-length σ xs)

  rename-atom : ∀ ρ {t} → Atom t → Atom (rename ρ t)
  rename-atom ρ a-type = a-type
  rename-atom ρ a-var = a-var
  rename-atom ρ a-global = a-global
  rename-atom ρ a-int-type = a-int-type
  rename-atom ρ a-int = a-int
  rename-atom ρ a-nat = a-nat
  rename-atom ρ a-bounded = a-bounded
  rename-atom ρ a-float-type = a-float-type
  rename-atom ρ a-float = a-float
  rename-atom ρ a-binary = a-binary
  rename-atom ρ a-atom-type = a-atom-type
  rename-atom ρ a-atom = a-atom
  rename-atom ρ a-hole = a-hole
  rename-atom ρ a-absurd = a-absurd

  mutual
    rename-step : ∀ ρ {t u} → t ⇛ u → rename ρ t ⇛ rename ρ u
    rename-step ρ (s-atom a) = s-atom (rename-atom ρ a)
    rename-step ρ (s-pi p q) = s-pi (rename-step ρ p) (rename-step (ext ρ) q)
    rename-step ρ (s-lam p q) = s-lam (rename-step ρ p) (rename-step (ext ρ) q)
    rename-step ρ (s-let p q r) = s-let (rename-step ρ p) (rename-step ρ q) (rename-step (ext ρ) r)
    rename-step ρ (s-app p q) = s-app (rename-step ρ p) (rename-step ρ q)
    rename-step ρ (s-data p q) = s-data (rename-terms ρ p) (rename-terms ρ q)
    rename-step ρ (s-ctor p) = s-ctor (rename-terms ρ p)
    rename-step ρ (s-case p q r) = s-case (rename-step ρ p) (rename-step ρ q) (rename-branches ρ r)
    rename-step ρ (s-effect-type p) = s-effect-type (rename-step ρ p)
    rename-step ρ (s-effect-pure p) = s-effect-pure (rename-step ρ p)
    rename-step ρ (s-effect-bind p q) = s-effect-bind (rename-step ρ p) (rename-step ρ q)
    rename-step ρ {t = t} (s-beta {b′ = b′} {a′ = a′} p q r) =
      subst (λ u → rename ρ t ⇛ u) (sym (rename-topSub ρ a′ b′))
        (s-beta (rename-step ρ p) (rename-step (ext ρ) q) (rename-step ρ r))
    rename-step ρ {t = t} (s-zeta {v′ = v′} {b′ = b′} p q r) =
      subst (λ u → rename ρ t ⇛ u) (sym (rename-topSub ρ v′ b′))
        (s-zeta (rename-step ρ p) (rename-step ρ q) (rename-step (ext ρ) r))
    rename-step ρ {t = t} (s-iota {bs′ = bs′} {c = c} {ar = ar} {b = b} {args = args} {args′ = args′} found len m bs xs) =
      subst (λ u → rename ρ t ⇛ u) (sym (rename-substArgs ρ args′ b))
        (subst (λ n → rename ρ t ⇛ substArgs (renameTerms ρ args′) (rename (ext^ n ρ) b))
          (sym (trans (terms-length xs) len))
          (s-iota (findBranch-rename ρ c bs′ found) (trans (rename-length ρ args) len)
            (rename-step ρ m) (rename-branches ρ bs) (rename-terms ρ xs)))
    rename-step ρ {t = t} (s-nat-zero {bs′ = bs′} {b = b} found m bs) =
      subst (λ u → rename ρ t ⇛ u) (sym (rename-substArgs ρ [] b))
        (s-nat-zero (findBranch-rename ρ "Z" bs′ found) (rename-step ρ m) (rename-branches ρ bs))
    rename-step ρ {t = t} (s-nat-suc {bs′ = bs′} {b = b} {n = n} found m bs) =
      subst (λ u → rename ρ t ⇛ u) (sym (rename-substArgs ρ (tm-nat_lit n ∷ []) b))
        (s-nat-suc (findBranch-rename ρ "S" bs′ found) (rename-step ρ m) (rename-branches ρ bs))
    rename-step ρ {t = t} (s-bounded-zero {bs′ = bs′} {b = b} found m bs) =
      subst (λ u → rename ρ t ⇛ u) (sym (rename-substArgs ρ (tm-nat_lit 0 ∷ []) b))
        (s-bounded-zero (findBranch-rename ρ "First" bs′ found) (rename-step ρ m) (rename-branches ρ bs))
    rename-step ρ {t = t} (s-bounded-suc {bs′ = bs′} {b = b} {n = n} found m bs) =
      subst (λ u → rename ρ t ⇛ u) (sym (rename-substArgs ρ (tm-nat_lit n ∷ tm-bounded_lit n ∷ []) b))
        (s-bounded-suc (findBranch-rename ρ "Next" bs′ found) (rename-step ρ m) (rename-branches ρ bs))
    rename-step ρ (s-delta found) =
      subst (λ u → tm-global _ ⇛ u) (sym (rename-closed (closed found))) (s-delta found)

    rename-terms : ∀ ρ {xs ys} → xs ⇛ᵗ ys → renameTerms ρ xs ⇛ᵗ renameTerms ρ ys
    rename-terms ρ st-nil = st-nil
    rename-terms ρ (st-cons p ps) = st-cons (rename-step ρ p) (rename-terms ρ ps)

    rename-branches : ∀ ρ {bs cs} → bs ⇛ᵇ cs → renameBranches ρ bs ⇛ᵇ renameBranches ρ cs
    rename-branches ρ sb-nil = sb-nil
    rename-branches ρ (sb-cons {ar = ar} p ps) =
      sb-cons (rename-step (ext^ ar ρ) p) (rename-branches ρ ps)

  extend-sub : ∀ {σ τ} → (∀ k → σ k ⇛ τ k) → ∀ k → extSub σ k ⇛ extSub τ k
  extend-sub h zero = s-atom a-var
  extend-sub h (suc k) = rename-step wk (h k)

  extend-subⁿ : ∀ n {σ τ} → (∀ k → σ k ⇛ τ k) → ∀ k → extSub^ n σ k ⇛ extSub^ n τ k
  extend-subⁿ zero h = h
  extend-subⁿ (suc n) h = extend-sub (extend-subⁿ n h)

  mutual
    substitute : ∀ σ τ → (∀ k → σ k ⇛ τ k)
      → ∀ {t u} → t ⇛ u → substS σ t ⇛ substS τ u
    substitute σ τ h (s-atom a-type) = s-atom a-type
    substitute σ τ h (s-atom (a-var {k})) = h k
    substitute σ τ h (s-atom a-global) = s-atom a-global
    substitute σ τ h (s-atom a-int-type) = s-atom a-int-type
    substitute σ τ h (s-atom a-int) = s-atom a-int
    substitute σ τ h (s-atom a-nat) = s-atom a-nat
    substitute σ τ h (s-atom a-bounded) = s-atom a-bounded
    substitute σ τ h (s-atom a-float-type) = s-atom a-float-type
    substitute σ τ h (s-atom a-float) = s-atom a-float
    substitute σ τ h (s-atom a-binary) = s-atom a-binary
    substitute σ τ h (s-atom a-atom-type) = s-atom a-atom-type
    substitute σ τ h (s-atom a-atom) = s-atom a-atom
    substitute σ τ h (s-atom a-hole) = s-atom a-hole
    substitute σ τ h (s-atom a-absurd) = s-atom a-absurd
    substitute σ τ h (s-pi p q) =
      s-pi (substitute σ τ h p) (substitute (extSub σ) (extSub τ) (extend-sub h) q)
    substitute σ τ h (s-lam p q) =
      s-lam (substitute σ τ h p) (substitute (extSub σ) (extSub τ) (extend-sub h) q)
    substitute σ τ h (s-let p q r) =
      s-let (substitute σ τ h p) (substitute σ τ h q) (substitute (extSub σ) (extSub τ) (extend-sub h) r)
    substitute σ τ h (s-app p q) = s-app (substitute σ τ h p) (substitute σ τ h q)
    substitute σ τ h (s-data p q) = s-data (substitute-terms σ τ h p) (substitute-terms σ τ h q)
    substitute σ τ h (s-ctor p) = s-ctor (substitute-terms σ τ h p)
    substitute σ τ h (s-case p q r) =
      s-case (substitute σ τ h p) (substitute σ τ h q) (substitute-branches σ τ h r)
    substitute σ τ h (s-effect-type p) = s-effect-type (substitute σ τ h p)
    substitute σ τ h (s-effect-pure p) = s-effect-pure (substitute σ τ h p)
    substitute σ τ h (s-effect-bind p q) = s-effect-bind (substitute σ τ h p) (substitute σ τ h q)
    substitute σ τ h {t = t} (s-beta {b′ = b′} {a′ = a′} p q r) =
      subst (λ u → substS σ t ⇛ u) (sym (subst-topSub τ a′ b′))
        (s-beta (substitute σ τ h p) (substitute (extSub σ) (extSub τ) (extend-sub h) q) (substitute σ τ h r))
    substitute σ τ h {t = t} (s-zeta {v′ = v′} {b′ = b′} p q r) =
      subst (λ u → substS σ t ⇛ u) (sym (subst-topSub τ v′ b′))
        (s-zeta (substitute σ τ h p) (substitute σ τ h q) (substitute (extSub σ) (extSub τ) (extend-sub h) r))
    substitute σ τ h {t = t} (s-iota {bs′ = bs′} {c = c} {ar = ar} {b = b} {args = args} {args′ = args′} found len m bs xs) =
      subst (λ u → substS σ t ⇛ u) (sym (subst-argsSub τ args′ b))
        (subst (λ n → substS σ t ⇛ substArgs (substTermsS τ args′) (substS (extSub^ n τ) b))
          (sym (trans (terms-length xs) len))
          (s-iota (findBranch-substBranchesS τ c bs′ found) (trans (subst-length σ args) len)
            (substitute σ τ h m) (substitute-branches σ τ h bs) (substitute-terms σ τ h xs)))
    substitute σ τ h {t = t} (s-nat-zero {bs′ = bs′} {b = b} found m bs) =
      subst (λ u → substS σ t ⇛ u) (sym (subst-argsSub τ [] b))
        (s-nat-zero (findBranch-substBranchesS τ "Z" bs′ found) (substitute σ τ h m) (substitute-branches σ τ h bs))
    substitute σ τ h {t = t} (s-nat-suc {bs′ = bs′} {b = b} {n = n} found m bs) =
      subst (λ u → substS σ t ⇛ u) (sym (subst-argsSub τ (tm-nat_lit n ∷ []) b))
        (s-nat-suc (findBranch-substBranchesS τ "S" bs′ found) (substitute σ τ h m) (substitute-branches σ τ h bs))
    substitute σ τ h {t = t} (s-bounded-zero {bs′ = bs′} {b = b} found m bs) =
      subst (λ u → substS σ t ⇛ u) (sym (subst-argsSub τ (tm-nat_lit 0 ∷ []) b))
        (s-bounded-zero (findBranch-substBranchesS τ "First" bs′ found) (substitute σ τ h m) (substitute-branches σ τ h bs))
    substitute σ τ h {t = t} (s-bounded-suc {bs′ = bs′} {b = b} {n = n} found m bs) =
      subst (λ u → substS σ t ⇛ u) (sym (subst-argsSub τ (tm-nat_lit n ∷ tm-bounded_lit n ∷ []) b))
        (s-bounded-suc (findBranch-substBranchesS τ "Next" bs′ found) (substitute σ τ h m) (substitute-branches σ τ h bs))
    substitute σ τ h (s-delta found) =
      subst (λ u → tm-global _ ⇛ u) (sym (substS-closed (closed found))) (s-delta found)

    substitute-terms : ∀ σ τ → (∀ k → σ k ⇛ τ k)
      → ∀ {xs ys} → xs ⇛ᵗ ys → substTermsS σ xs ⇛ᵗ substTermsS τ ys
    substitute-terms σ τ h st-nil = st-nil
    substitute-terms σ τ h (st-cons p ps) = st-cons (substitute σ τ h p) (substitute-terms σ τ h ps)

    substitute-branches : ∀ σ τ → (∀ k → σ k ⇛ τ k)
      → ∀ {bs cs} → bs ⇛ᵇ cs → substBranchesS σ bs ⇛ᵇ substBranchesS τ cs
    substitute-branches σ τ h sb-nil = sb-nil
    substitute-branches σ τ h (sb-cons {ar = ar} p ps) =
      sb-cons (substitute (extSub^ ar σ) (extSub^ ar τ) (extend-subⁿ ar h) p) (substitute-branches σ τ h ps)

  substitute-top : ∀ {a a′ b b′} → a ⇛ a′ → b ⇛ b′ → substTopT a b ⇛ substTopT a′ b′
  substitute-top {a} {a′} p q =
    substitute (topSub a) (topSub a′) (λ { zero → p ; (suc k) → s-atom a-var }) q

  args-pointwise : ∀ {xs ys} → xs ⇛ᵗ ys → ∀ n k → argsSub-go n xs k ⇛ argsSub-go n ys k
  args-pointwise st-nil n k = s-atom a-var
  args-pointwise (st-cons p ps) n zero = p
  args-pointwise (st-cons p ps) n (suc k) = args-pointwise ps (suc n) k

  substitute-args : ∀ {xs ys b b′} → xs ⇛ᵗ ys → b ⇛ b′ → substArgs xs b ⇛ substArgs ys b′
  substitute-args {xs} {ys} ps p = substitute (argsSub xs) (argsSub ys) (args-pointwise ps 0) p

  lookup-step : ∀ c {bs cs ar b} → bs ⇛ᵇ cs
    → findBranch c bs ≡ just (c , ar , b)
    → ∃ λ b′ → findBranch c cs ≡ just (c , ar , b′) × b ⇛ b′
  lookup-step c sb-nil ()
  lookup-step c (sb-cons {cn = cn} {b′ = b′} p ps) found with c ≟ cn
  ... | yes refl =
    b′ , cong (λ q → just (c , proj₁ (proj₂ q) , b′)) (just-inj found)
       , subst (λ b → b ⇛ b′) (cong (λ q → proj₂ (proj₂ q)) (just-inj found)) p
  ... | no different = lookup-step c ps found

  lookup-unique : ∀ c bs {ar b ar′ b′}
    → findBranch c bs ≡ just (c , ar , b) → findBranch c bs ≡ just (c , ar′ , b′)
    → ar ≡ ar′ × b ≡ b′
  lookup-unique c bs p q with just-inj (trans (sym p) q)
  ... | refl = refl , refl

  mutual
    -- The conclusion is ONE step on BOTH sides, not local joinability.
    diamond : Diamond _⇛_
    diamond (s-atom a) (s-atom b) = _ , s-atom a , s-atom b
    diamond (s-atom a-global) (s-delta found) = _ , s-delta found , reflexive _
    diamond (s-delta found) (s-atom a-global) = _ , reflexive _ , s-delta found
    diamond (s-delta p) (s-delta q) with just-inj (trans (sym p) q)
    ... | refl = _ , reflexive _ , reflexive _
    diamond (s-pi p q) (s-pi p′ q′)
      with diamond p p′ | diamond q q′
    ... | d , dd , de | c , cd , ce = _ , s-pi dd cd , s-pi de ce
    diamond (s-lam p q) (s-lam p′ q′)
      with diamond p p′ | diamond q q′
    ... | d , dd , de | b , bd , be = _ , s-lam dd bd , s-lam de be
    diamond (s-app p q) (s-app p′ q′)
      with diamond p p′ | diamond q q′
    ... | f , fd , fe | a , ad , ae = _ , s-app fd ad , s-app fe ae
    diamond (s-data p q) (s-data p′ q′)
      with terms-diamond p p′ | terms-diamond q q′
    ... | ps , pd , pe | is , id , ie = _ , s-data pd id , s-data pe ie
    diamond (s-ctor p) (s-ctor q) with terms-diamond p q
    ... | args , ad , ae = _ , s-ctor ad , s-ctor ae
    diamond (s-effect-type p) (s-effect-type q) with diamond p q
    ... | a , ad , ae = _ , s-effect-type ad , s-effect-type ae
    diamond (s-effect-pure p) (s-effect-pure q) with diamond p q
    ... | a , ad , ae = _ , s-effect-pure ad , s-effect-pure ae
    diamond (s-effect-bind p q) (s-effect-bind p′ q′)
      with diamond p p′ | diamond q q′
    ... | e , ed , ee | k , kd , ke = _ , s-effect-bind ed kd , s-effect-bind ee ke
    diamond (s-let p q r) (s-let p′ q′ r′)
      with diamond p p′ | diamond q q′ | diamond r r′
    ... | ty , td , te | v , vd , ve | b , bd , be =
      _ , s-let td vd bd , s-let te ve be
    diamond (s-zeta p q r) (s-zeta p′ q′ r′)
      with diamond q q′ | diamond r r′
    ... | v , vd , ve | b , bd , be =
      _ , substitute-top vd bd , substitute-top ve be
    diamond (s-zeta p q r) (s-let p′ q′ r′)
      with diamond q q′ | diamond r r′
    ... | v , vd , ve | b , bd , be =
      _ , substitute-top vd bd , s-zeta (reflexive _) ve be
    diamond (s-let p q r) (s-zeta p′ q′ r′)
      with diamond q q′ | diamond r r′
    ... | v , vd , ve | b , bd , be =
      _ , s-zeta (reflexive _) vd bd , substitute-top ve be
    diamond (s-beta p q r) (s-beta p′ q′ r′)
      with diamond q q′ | diamond r r′
    ... | b , bd , be | a , ad , ae =
      _ , substitute-top ad bd , substitute-top ae be
    diamond (s-beta p q r) (s-app (s-lam p′ q′) r′)
      with diamond q q′ | diamond r r′
    ... | b , bd , be | a , ad , ae =
      _ , substitute-top ad bd , s-beta (reflexive _) be ae
    diamond (s-app (s-lam p q) r) (s-beta p′ q′ r′)
      with diamond q q′ | diamond r r′
    ... | b , bd , be | a , ad , ae =
      _ , s-beta (reflexive _) bd ad , substitute-top ae be

    diamond (s-iota {c = c} found refl m bs xs) (s-iota found′ refl m′ cs ys)
      with terms-diamond xs ys | branches-diamond bs cs
    ... | args , ad , ae | branches , bd , be
      with lookup-step c bd found | lookup-step c be found′
    ... | b , fb , bb | b′ , fb′ , bb′ with lookup-unique c branches fb fb′
    ... | refl , refl = _ , substitute-args ad bb , substitute-args ae bb′

    diamond (s-iota {c = c} found refl m bs xs) (s-case (s-ctor ys) m′ cs)
      with terms-diamond xs ys | branches-diamond bs cs
    ... | args , ad , ae | branches , bd , be with lookup-step c bd found
    ... | b , fb , bb =
      _ , substitute-args ad bb , s-iota fb (terms-length ys) (reflexive _) be ae
    diamond (s-case (s-ctor xs) m bs) (s-iota {c = c} found refl m′ cs ys)
      with terms-diamond xs ys | branches-diamond bs cs
    ... | args , ad , ae | branches , bd , be with lookup-step c be found
    ... | b , fb , bb =
      _ , s-iota fb (terms-length xs) (reflexive _) bd ad , substitute-args ae bb

    diamond (s-nat-zero found m bs) (s-nat-zero found′ m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "Z" bd found | lookup-step "Z" be found′
    ... | b , fb , bb | b′ , fb′ , bb′ with lookup-unique "Z" branches fb fb′
    ... | refl , refl = _ , substitute-args st-nil bb , substitute-args st-nil bb′
    diamond (s-nat-zero found m bs) (s-case (s-atom a-nat) m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "Z" bd found
    ... | b , fb , bb = _ , substitute-args st-nil bb , s-nat-zero fb (reflexive _) be
    diamond (s-case (s-atom a-nat) m bs) (s-nat-zero found m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "Z" be found
    ... | b , fb , bb = _ , s-nat-zero fb (reflexive _) bd , substitute-args st-nil bb

    diamond (s-nat-suc {n = n} found m bs) (s-nat-suc found′ m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "S" bd found | lookup-step "S" be found′
    ... | b , fb , bb | b′ , fb′ , bb′ with lookup-unique "S" branches fb fb′
    ... | refl , refl =
      _ , substitute-args (terms-refl (tm-nat_lit n ∷ [])) bb
        , substitute-args (terms-refl (tm-nat_lit n ∷ [])) bb′
    diamond (s-nat-suc {n = n} found m bs) (s-case (s-atom a-nat) m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "S" bd found
    ... | b , fb , bb =
      _ , substitute-args (terms-refl (tm-nat_lit n ∷ [])) bb , s-nat-suc fb (reflexive _) be
    diamond (s-case (s-atom a-nat) m bs) (s-nat-suc {n = n} found m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "S" be found
    ... | b , fb , bb =
      _ , s-nat-suc fb (reflexive _) bd , substitute-args (terms-refl (tm-nat_lit n ∷ [])) bb

    diamond (s-bounded-zero found m bs) (s-bounded-zero found′ m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "First" bd found | lookup-step "First" be found′
    ... | b , fb , bb | b′ , fb′ , bb′ with lookup-unique "First" branches fb fb′
    ... | refl , refl =
      _ , substitute-args (terms-refl (tm-nat_lit 0 ∷ [])) bb
        , substitute-args (terms-refl (tm-nat_lit 0 ∷ [])) bb′
    diamond (s-bounded-zero found m bs) (s-case (s-atom a-bounded) m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "First" bd found
    ... | b , fb , bb =
      _ , substitute-args (terms-refl (tm-nat_lit 0 ∷ [])) bb , s-bounded-zero fb (reflexive _) be
    diamond (s-case (s-atom a-bounded) m bs) (s-bounded-zero found m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "First" be found
    ... | b , fb , bb =
      _ , s-bounded-zero fb (reflexive _) bd , substitute-args (terms-refl (tm-nat_lit 0 ∷ [])) bb

    diamond (s-bounded-suc {n = n} found m bs) (s-bounded-suc found′ m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "Next" bd found | lookup-step "Next" be found′
    ... | b , fb , bb | b′ , fb′ , bb′ with lookup-unique "Next" branches fb fb′
    ... | refl , refl =
      _ , substitute-args (terms-refl (tm-nat_lit n ∷ tm-bounded_lit n ∷ [])) bb
        , substitute-args (terms-refl (tm-nat_lit n ∷ tm-bounded_lit n ∷ [])) bb′
    diamond (s-bounded-suc {n = n} found m bs) (s-case (s-atom a-bounded) m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "Next" bd found
    ... | b , fb , bb =
      _ , substitute-args (terms-refl (tm-nat_lit n ∷ tm-bounded_lit n ∷ [])) bb
        , s-bounded-suc fb (reflexive _) be
    diamond (s-case (s-atom a-bounded) m bs) (s-bounded-suc {n = n} found m′ cs)
      with branches-diamond bs cs
    ... | branches , bd , be with lookup-step "Next" be found
    ... | b , fb , bb =
      _ , s-bounded-suc fb (reflexive _) bd
        , substitute-args (terms-refl (tm-nat_lit n ∷ tm-bounded_lit n ∷ [])) bb

    diamond (s-case p q r) (s-case p′ q′ r′)
      with diamond p p′ | diamond q q′ | branches-diamond r r′
    ... | s , sd , se | m , md , me | bs , bd , be =
      _ , s-case sd md bd , s-case se me be

    terms-diamond : Diamond _⇛ᵗ_
    terms-diamond st-nil st-nil = [] , st-nil , st-nil
    terms-diamond (st-cons p ps) (st-cons q qs)
      with diamond p q | terms-diamond ps qs
    ... | x , xd , xe | xs , xsd , xse =
      x ∷ xs , st-cons xd xsd , st-cons xe xse

    branches-diamond : Diamond _⇛ᵇ_
    branches-diamond sb-nil sb-nil = [] , sb-nil , sb-nil
    branches-diamond (sb-cons {cn = cn} {ar = ar} p ps) (sb-cons q qs)
      with diamond p q | branches-diamond ps qs
    ... | b , bd , be | bs , bsd , bse =
      (cn , ar , b) ∷ bs , sb-cons bd bsd , sb-cons be bse

  module Joined = Closure _⇛_ diamond

  -- Original small-step confluence statement, with unchanged hypotheses
  -- and semantics. Closure recursion is checked independently above.
  confluence : ∀ {t u v} → _⇝*_ sig t u → _⇝*_ sig t v
    → ∃ λ w → _⇝*_ sig u w × _⇝*_ sig v w
  confluence p q with Joined.confluent (from-small-star p) (from-small-star q)
  ... | w , uw , vw = w , to-small uw , to-small vw

  NormalForm : Term → Set
  NormalForm t = ∀ {u} → _⇝_ sig t u → ⊥

  normal-path : ∀ {t u} → NormalForm t → _⇝*_ sig t u → t ≡ u
  normal-path nf ⇝*-refl = refl
  normal-path nf (⇝*-step p ps) = ⊥-elim (nf p)

  normal-forms-unique : ∀ {t u v} → _⇝*_ sig t u → _⇝*_ sig t v
    → NormalForm u → NormalForm v → u ≡ v
  normal-forms-unique p q nu nv with confluence p q
  ... | w , uw , vw = trans (normal-path nu uw) (sym (normal-path nv vw))
