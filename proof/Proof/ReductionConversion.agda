------------------------------------------------------------------------
-- A reduction-compatible conversion model for the CURRENT formal Core.
-- Compact literals expand to ordinary constructor towers; equality means
-- a common reduct in the expanded signature. No values are collapsed.
-- This is not an executable NbE/eta refinement or a dependent-scope repair.
------------------------------------------------------------------------
module Proof.ReductionConversion where

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Syntax
open import Core.TypeHeads
open import Core.Typing using (Conversion; All2; a2[]; a2∷)
open import Core.Reduction
open import Core.Relation using (map-star)
open import Core.LiteralExpansion
open import Proof.Confluence using (ClosedBody)
import Proof.StrictConfluence as Strict
import Proof.ExpansionSimulation as Sim

module Model (sig : Signature) (closed : ClosedBody sig) where
  esig = expandSig sig
  module C = Strict.Laws esig
    (λ {f} {b} p → expanded-body-closed sig
      (λ {f} {b} q → closed {f} {b} q) {f} {b} p)
  module E = Sim.Simulation sig
  module O = C.O

  infix 4 _~_ _≈_
  _~_ : Term → Term → Set
  t ~ u = ∃ λ w → _⇝*_ esig t w × _⇝*_ esig u w

  _≈_ : Term → Term → Set
  t ≈ u = expand t ~ expand u

  join-refl : ∀ {t} → t ~ t
  join-refl {t} = t , ⇝*-refl , ⇝*-refl

  join-sym : ∀ {t u} → t ~ u → u ~ t
  join-sym (w , p , q) = w , q , p

  join-trans : ∀ {t u v} → t ~ u → u ~ v → t ~ v
  join-trans (w , tw , uw) (z , uz , vz) with C.confluence uw uz
  ... | k , wk , zk = k , O.⇝*-trans tw wk , O.⇝*-trans vz zk

  rename-path : ∀ ρ {t u} → _⇝*_ esig t u → _⇝*_ esig (rename ρ t) (rename ρ u)
  rename-path ρ p =
    C.to-small (map-star (rename ρ) (C.rename-step ρ) (C.from-small-star p))

  subst-path : ∀ σ {t u} → _⇝*_ esig t u → _⇝*_ esig (substS σ t) (substS σ u)
  subst-path σ p =
    C.to-small (map-star (substS σ)
      (C.substitute σ σ (λ k → C.reflexive (σ k))) (C.from-small-star p))

  extend-paths : ∀ {σ τ} → (∀ k → _⇝*_ esig (σ k) (τ k))
    → ∀ k → _⇝*_ esig (extSub σ k) (extSub τ k)
  extend-paths h zero = ⇝*-refl
  extend-paths h (suc k) = rename-path wk (h k)

  extend-pathsⁿ : ∀ n {σ τ} → (∀ k → _⇝*_ esig (σ k) (τ k))
    → ∀ k → _⇝*_ esig (extSub^ n σ k) (extSub^ n τ k)
  extend-pathsⁿ zero h = h
  extend-pathsⁿ (suc n) h = extend-paths (extend-pathsⁿ n h)

  mutual
    -- Pointwise finite paths need not have a uniform length. Recurse on
    -- the term, not on a purported maximum over all substitution entries.
    subst-paths : ∀ t σ τ → (∀ k → _⇝*_ esig (σ k) (τ k))
      → _⇝*_ esig (substS σ t) (substS τ t)
    subst-paths (tm-type l) σ τ h = ⇝*-refl
    subst-paths (tm-var k) σ τ h = h k
    subst-paths (tm-pi g d c) σ τ h =
      O.⇝*-trans (O.⇝*-pi-dom (subst-paths d σ τ h))
        (O.⇝*-pi-cod (subst-paths c (extSub σ) (extSub τ) (extend-paths h)))
    subst-paths (tm-lam g d b) σ τ h =
      O.⇝*-trans (O.⇝*-lam-dom (subst-paths d σ τ h))
        (O.⇝*-lam-body (subst-paths b (extSub σ) (extSub τ) (extend-paths h)))
    subst-paths (tm-let g ty v b) σ τ h =
      O.⇝*-trans (O.⇝*-let-ty (subst-paths ty σ τ h))
        (O.⇝*-trans (O.⇝*-let-val (subst-paths v σ τ h))
          (O.⇝*-let-body (subst-paths b (extSub σ) (extSub τ) (extend-paths h))))
    subst-paths (tm-app f a) σ τ h =
      O.⇝*-trans (O.⇝*-app₁ (subst-paths f σ τ h)) (O.⇝*-app₂ (subst-paths a σ τ h))
    subst-paths (tm-data n ps is) σ τ h =
      O.⇝*-trans (E.params-path (subst-paths-terms ps σ τ h))
        (E.indices-path (subst-paths-terms is σ τ h))
    subst-paths (tm-ctor n args) σ τ h = E.ctor-path (subst-paths-terms args σ τ h)
    subst-paths (tm-case s m bs) σ τ h =
      O.⇝*-trans (O.⇝*-case (subst-paths s σ τ h))
        (O.⇝*-trans (O.⇝*-case-motive (subst-paths m σ τ h))
          (O.⇝*-case-brs (subst-paths-branches bs σ τ h)))
    subst-paths (tm-global n) σ τ h = ⇝*-refl
    subst-paths tm-int_type σ τ h = ⇝*-refl
    subst-paths (tm-int_lit k) σ τ h = ⇝*-refl
    subst-paths (tm-nat_lit k) σ τ h = ⇝*-refl
    subst-paths (tm-bounded_lit k) σ τ h = ⇝*-refl
    subst-paths tm-float_type σ τ h = ⇝*-refl
    subst-paths tm-float_lit σ τ h = ⇝*-refl
    subst-paths tm-binary_type σ τ h = ⇝*-refl
    subst-paths tm-atom_type σ τ h = ⇝*-refl
    subst-paths (tm-atom_lit n) σ τ h = ⇝*-refl
    subst-paths (tm-effect_type a) σ τ h = O.⇝*-effect_type (subst-paths a σ τ h)
    subst-paths (tm-effect_pure a) σ τ h = O.⇝*-effect_pure (subst-paths a σ τ h)
    subst-paths (tm-effect_bind e k) σ τ h =
      O.⇝*-trans (O.⇝*-effect_bind₁ (subst-paths e σ τ h)) (O.⇝*-effect_bind₂ (subst-paths k σ τ h))
    subst-paths (tm-hole n) σ τ h = ⇝*-refl
    subst-paths tm-absurd σ τ h = ⇝*-refl

    subst-paths-terms : ∀ ts σ τ → (∀ k → _⇝*_ esig (σ k) (τ k))
      → O._⇉*ᵗ*_ (substTermsS σ ts) (substTermsS τ ts)
    subst-paths-terms [] σ τ h = O.⇉ᵗ*-nil
    subst-paths-terms (x ∷ xs) σ τ h =
      O.⇉ᵗ*-cons (O.⇝→⇉* (subst-paths x σ τ h)) (subst-paths-terms xs σ τ h)

    subst-paths-branches : ∀ bs σ τ → (∀ k → _⇝*_ esig (σ k) (τ k))
      → _⇝*ᵇ_ esig (substBranchesS σ bs) (substBranchesS τ bs)
    subst-paths-branches [] σ τ h = ⇝ᵇ-nil
    subst-paths-branches ((cn , ar , b) ∷ bs) σ τ h =
      ⇝ᵇ-cons (subst-paths b (extSub^ ar σ) (extSub^ ar τ) (extend-pathsⁿ ar h))
        (subst-paths-branches bs σ τ h)

  model-rename : ∀ {t u} ρ → t ≈ u → rename ρ t ≈ rename ρ u
  model-rename {t} {u} ρ (w , p , q) =
    rename ρ w ,
      subst (λ x → _⇝*_ esig x (rename ρ w)) (sym (expand-rename ρ t)) (rename-path ρ p) ,
      subst (λ x → _⇝*_ esig x (rename ρ w)) (sym (expand-rename ρ u)) (rename-path ρ q)

  model-subst : ∀ {t u} σ → t ≈ u → substS σ t ≈ substS σ u
  model-subst {t} {u} σ (w , p , q) =
    substS (expandSub σ) w ,
      subst (λ x → _⇝*_ esig x (substS (expandSub σ) w))
        (sym (expand-subst σ t)) (subst-path (expandSub σ) p) ,
      subst (λ x → _⇝*_ esig x (substS (expandSub σ) w))
        (sym (expand-subst σ u)) (subst-path (expandSub σ) q)

  model-subst-cong : ∀ {t σ τ} → (∀ k → σ k ≈ τ k) → substS σ t ≈ substS τ t
  model-subst-cong {t} {σ} {τ} h =
    substS (λ k → proj₁ (h k)) (expand t) ,
      subst (λ x → _⇝*_ esig x (substS (λ k → proj₁ (h k)) (expand t)))
        (sym (expand-subst σ t))
        (subst-paths (expand t) (expandSub σ) (λ k → proj₁ (h k)) (λ k → proj₁ (proj₂ (h k)))) ,
      subst (λ x → _⇝*_ esig x (substS (λ k → proj₁ (h k)) (expand t)))
        (sym (expand-subst τ t))
        (subst-paths (expand t) (expandSub τ) (λ k → proj₁ (h k)) (λ k → proj₂ (proj₂ (h k))))

  rigid-step : ∀ {t u h} → HasTypeHead t h → _⇝_ esig t u → HasTypeHead u h
  rigid-step ty-pi (ξ-pi-dom p) = ty-pi
  rigid-step ty-pi (ξ-pi-cod p) = ty-pi
  rigid-step ty-data (ξ-data-params-at i p) = ty-data
  rigid-step ty-data (ξ-data-indices-at i p) = ty-data
  rigid-step ty-effect (ξ-effect_type p) = ty-effect

  rigid-path : ∀ {t u h} → HasTypeHead t h → _⇝*_ esig t u → HasTypeHead u h
  rigid-path ht ⇝*-refl = ht
  rigid-path ht (⇝*-step p ps) = rigid-path (rigid-step ht p) ps

  model-heads : ∀ {t u h h′} → HasTypeHead t h → HasTypeHead u h′ → t ≈ u → h ≡ h′
  model-heads ht hu (w , p , q) =
    type-head-unique (rigid-path (expand-head ht) p) (rigid-path (expand-head hu) q)

  pi-path : ∀ {g d c u} → _⇝*_ esig (tm-pi g d c) u
    → ∃ λ d′ → ∃ λ c′ → u ≡ tm-pi g d′ c′ × _⇝*_ esig d d′ × _⇝*_ esig c c′
  pi-path ⇝*-refl = _ , _ , refl , ⇝*-refl , ⇝*-refl
  pi-path (⇝*-step (ξ-pi-dom p) ps) with pi-path ps
  ... | d′ , c′ , eq , dp , cp = d′ , c′ , eq , ⇝*-step p dp , cp
  pi-path (⇝*-step (ξ-pi-cod p) ps) with pi-path ps
  ... | d′ , c′ , eq , dp , cp = d′ , c′ , eq , dp , ⇝*-step p cp

  pi-shape : ∀ {g d c g′ d′ c′} → tm-pi g d c ≡ tm-pi g′ d′ c′
    → g ≡ g′ × d ≡ d′ × c ≡ c′
  pi-shape refl = refl , refl , refl

  pi-join : ∀ {g d c g′ d′ c′}
    → tm-pi g′ d′ c′ ~ tm-pi g d c → g′ ≡ g × (d′ ~ d) × (c′ ~ c)
  pi-join (w , p , q) with pi-path p | pi-path q
  ... | d₁ , c₁ , eq₁ , dp , cp | d₂ , c₂ , eq₂ , dq , cq
    with pi-shape (trans (sym eq₁) eq₂)
  ... | refl , refl , refl = refl , (d₁ , dp , dq) , (c₁ , cp , cq)

  spine-joins : ∀ {xs ys} → All2 _≈_ xs ys
    → ∃ λ zs → O._⇉*ᵗ*_ (expandTerms xs) zs × O._⇉*ᵗ*_ (expandTerms ys) zs
  spine-joins a2[] = [] , O.⇉ᵗ*-nil , O.⇉ᵗ*-nil
  spine-joins (a2∷ (w , p , q) ps) with spine-joins ps
  ... | ws , lp , lq = w ∷ ws , O.⇉ᵗ*-cons (O.⇝→⇉* p) lp , O.⇉ᵗ*-cons (O.⇝→⇉* q) lq

  model-pi : ∀ {g d d′ c c′} → d ≈ d′ → c ≈ c′ → tm-pi g d c ≈ tm-pi g d′ c′
  model-pi {g} (d , dp , dq) (c , cp , cq) =
    tm-pi g d c , O.⇝*-trans (O.⇝*-pi-dom dp) (O.⇝*-pi-cod cp) ,
      O.⇝*-trans (O.⇝*-pi-dom dq) (O.⇝*-pi-cod cq)

  model-app : ∀ {f f′ a a′} → f ≈ f′ → a ≈ a′ → tm-app f a ≈ tm-app f′ a′
  model-app (f , fp , fq) (a , ap , aq) =
    tm-app f a , O.⇝*-trans (O.⇝*-app₁ fp) (O.⇝*-app₂ ap) ,
      O.⇝*-trans (O.⇝*-app₁ fq) (O.⇝*-app₂ aq)

  model-data : ∀ {n ps ps′ is is′} → All2 _≈_ ps ps′ → All2 _≈_ is is′
    → tm-data n ps is ≈ tm-data n ps′ is′
  model-data {n} ps is with spine-joins ps | spine-joins is
  ... | ws , pp , pq | vs , ip , iq =
    tm-data n ws vs , O.⇝*-trans (E.params-path pp) (E.indices-path ip) ,
      O.⇝*-trans (E.params-path pq) (E.indices-path iq)

  model-ctor : ∀ {n xs ys} → All2 _≈_ xs ys → tm-ctor n xs ≈ tm-ctor n ys
  model-ctor {n} ps with spine-joins ps
  ... | ws , pp , pq = tm-ctor n ws , E.ctor-path pp , E.ctor-path pq

  model-effect-type : ∀ {t u} → t ≈ u → tm-effect_type t ≈ tm-effect_type u
  model-effect-type (w , p , q) = tm-effect_type w , O.⇝*-effect_type p , O.⇝*-effect_type q
  model-effect-pure : ∀ {t u} → t ≈ u → tm-effect_pure t ≈ tm-effect_pure u
  model-effect-pure (w , p , q) = tm-effect_pure w , O.⇝*-effect_pure p , O.⇝*-effect_pure q
  model-effect-bind : ∀ {e e′ k k′} → e ≈ e′ → k ≈ k′ → tm-effect_bind e k ≈ tm-effect_bind e′ k′
  model-effect-bind (e , ep , eq) (k , kp , kq) =
    tm-effect_bind e k , O.⇝*-trans (O.⇝*-effect_bind₁ ep) (O.⇝*-effect_bind₂ kp) ,
      O.⇝*-trans (O.⇝*-effect_bind₁ eq) (O.⇝*-effect_bind₂ kq)

  conversion : Conversion
  conversion = record
    { _≈_ = _≈_
    ; ≈-refl = λ {t} → join-refl {expand t}
    ; ≈-sym = λ {t} {u} → join-sym {expand t} {expand u}
    ; ≈-trans = λ {t} {u} {v} → join-trans {expand t} {expand u} {expand v}
    ; ≈-pi = λ {g} {d} {d′} {c} {c′} → model-pi {g} {d} {d′} {c} {c′}
    ; ≈-app = λ {f} {f′} {a} {a′} → model-app {f} {f′} {a} {a′}
    ; ≈-data = model-data
    ; ≈-ctor = model-ctor
    ; ≈-effect_type = λ {t} {u} → model-effect-type {t} {u}
    ; ≈-effect_pure = λ {t} {u} → model-effect-pure {t} {u}
    ; ≈-effect_bind = λ {e} {e′} {k} {k′} → model-effect-bind {e} {e′} {k} {k′}
    ; ≈-rename = λ {t} {u} → model-rename {t} {u}
    ; ≈-subst = λ {t} {u} → model-subst {t} {u}
    ; ≈-subst-cong = λ {t} {σ} {τ} → model-subst-cong {t} {σ} {τ}
    ; ≈-heads = λ {t} {u} → model-heads {t} {u}
    ; ≈-pi-components = λ {g} {d} {c} {g′} {d′} {c′} →
        pi-join {g} {expand d} {expand c} {g′} {expand d′} {expand c′}
    ; ≈-nat-zero = _ , ⇝*-refl , ⇝*-refl
    ; ≈-nat-suc = _ , ⇝*-refl , ⇝*-refl
    ; ≈-bounded-zero = _ , ⇝*-refl , ⇝*-refl
    ; ≈-bounded-suc = _ , ⇝*-refl , ⇝*-refl
    }

  -- Precisely the FULL ReduceConv contract, for the ORIGINAL signature.
  reduce-converts : ∀ {t u} → _⇝_ sig t u → Conversion._≈_ conversion t u
  reduce-converts {u = u} p = expand u , E.expand-step p , ⇝*-refl
