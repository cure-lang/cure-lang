------------------------------------------------------------------------
-- General positive MODEL evaluation refinement. A closure denotes its
-- captured syntax, not an asserted fully normalized Quote result.
-- No evaluator-totality, preservation or normalization oracle is input.
------------------------------------------------------------------------
module Proof.ClosureEvaluation where
import Data.Empty

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _<_; _∸_)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Core.Syntax
open import Core.Signature using (nothing≠just; just-inj)
open import Core.Reduction using (Signature; _⇝*_; ⇝*-refl; ⇝*-step; β; ζ)
import Core.ClosureEval as E
import Core.LocalFrame as F
import Core.Parallel as Parallel
import Proof.Substitution as Substitution
import Core.FlatContext as Flat
import Data.Vec as Vec

embed-flat : Flat.Value → E.Value
embed-flat (Flat.sort l) = E.v-type l
embed-flat Flat.atom-type = E.v-atom-type
embed-flat (Flat.atom name) = E.v-atom name
embed-flat (Flat.neutral level) = E.v-neutral (E.n-var level)

environment-sub : List Term → Sub
environment-sub terms = F.prefix terms F.identity

mutual
  data Denotes (depth : ℕ) : E.Value → Term → Set where
    d-type : ∀ {l} → Denotes depth (E.v-type l) (tm-type l)
    d-atom-type : Denotes depth E.v-atom-type tm-atom_type
    d-atom : ∀ {name} → Denotes depth (E.v-atom name) (tm-atom_lit name)
    d-pi : ∀ {g domain env body A terms}
      → Denotes depth domain A → Environments depth env terms
      → Denotes depth (E.v-pi g domain env body) (tm-pi g A (substS (extSub (environment-sub terms)) body))
    d-lam : ∀ {g domain env body A terms}
      → Denotes depth domain A → Environments depth env terms
      → Denotes depth (E.v-lam g domain env body) (tm-lam g A (substS (extSub (environment-sub terms)) body))
    d-neutral : ∀ {neutral term} → Neutrals depth neutral term → Denotes depth (E.v-neutral neutral) term
  data Environments (depth : ℕ) : List E.Value → List Term → Set where
    d[] : Environments depth [] []
    d∷ : ∀ {value term env terms}
      → Denotes depth value term → Environments depth env terms
      → Environments depth (value ∷ env) (term ∷ terms)
  data Neutrals (depth : ℕ) : E.Neutral → Term → Set where
    d-var : ∀ {level} → level < depth → Neutrals depth (E.n-var level) (tm-var (depth ∸ suc level))
    d-global : ∀ {name} → Neutrals depth (E.n-global name) (tm-global name)
    d-app : ∀ {function argument f a}
      → Neutrals depth function f → Denotes depth argument a → Neutrals depth (E.n-app function argument) (tm-app f a)

flat-denotation : ∀ {depth value term} → Flat.Reads depth value term → Denotes depth (embed-flat value) term
flat-denotation Flat.q-sort = d-type
flat-denotation Flat.q-atom-type = d-atom-type
flat-denotation Flat.q-atom = d-atom
flat-denotation (Flat.q-neutral inside) = d-neutral (d-var inside)
flat-environment : ∀ {depth n} {values : Vec.Vec Flat.Value n} {terms}
  → Flat.ReadValues depth values terms
  → Environments depth (Data.List.map embed-flat (Vec.toList values)) (Vec.toList terms)
flat-environment Flat.q[] = d[]
flat-environment (Flat.q∷ head rest) = d∷ (flat-denotation head) (flat-environment rest)

lookup-denotation : ∀ {d env terms k value} → Environments d env terms
  → E.lookup-value env k ≡ just value
  → ∃ λ term → Denotes d value term × environment-sub terms k ≡ term
lookup-denotation d[] found = Data.Empty.⊥-elim (nothing≠just found)
lookup-denotation {k = zero} (d∷ {term = term} head rest) found with just-inj found
... | refl = term , head , refl
lookup-denotation {k = suc k} (d∷ head rest) found = lookup-denotation rest found

extension : ∀ argument σ k → Substitution.substCompose (topSub argument) (extSub σ) k ≡ F.push argument σ k
extension argument σ zero = refl
extension argument σ (suc k) = Substitution.topSub-rename argument (σ k)
beta-environment : ∀ argument σ body
  → substTopT argument (substS (extSub σ) body) ≡ substS (F.push argument σ) body
beta-environment argument σ body =
  trans (Substitution.subst-compose (topSub argument) (extSub σ) body)
    (cong (λ τ → substS τ body) (funext (extension argument σ)))

module Simulation (sig : Signature) where
  module O = Parallel.Par sig
  equal-path : ∀ {t u} → t ≡ u → _⇝*_ sig t u
  equal-path refl = ⇝*-refl

  mutual
    evaluate : ∀ {depth env terms term value} → Environments depth env terms → E.Evaluates env term value
      → ∃ λ result → Denotes depth value result × _⇝*_ sig (substS (environment-sub terms) term) result
    evaluate env E.e-type = _ , d-type , ⇝*-refl
    evaluate env E.e-atom-type = _ , d-atom-type , ⇝*-refl
    evaluate env E.e-atom = _ , d-atom , ⇝*-refl
    evaluate env E.e-global = _ , d-neutral d-global , ⇝*-refl
    evaluate env (E.e-var found) with lookup-denotation env found
    ... | term , denoted , equal = term , denoted , equal-path equal
    evaluate env (E.e-pi domain) with evaluate env domain
    ... | A , denoted , path = _ , d-pi denoted env , O.⇝*-pi-dom path
    evaluate env (E.e-lam domain) with evaluate env domain
    ... | A , denoted , path = _ , d-lam denoted env , O.⇝*-lam-dom path
    evaluate env (E.e-app function argument applied)
      with evaluate env function | evaluate env argument
    ... | f , function-denoted , function-path | a , argument-denoted , argument-path
      with application function-denoted argument-denoted applied
    ... | result , denoted , path = result , denoted ,
      O.⇝*-trans (O.⇝*-app₁ function-path) (O.⇝*-trans (O.⇝*-app₂ argument-path) path)
    evaluate {terms = terms} env (E.e-let {body = body} value body-evaluated) with evaluate env value
    ... | actual , value-denoted , value-path with evaluate (d∷ value-denoted env) body-evaluated
    ... | result , denoted , body-path = result , denoted ,
      O.⇝*-trans (O.⇝*-let-val value-path)
        (⇝*-step ζ (O.⇝*-trans (equal-path (beta-environment actual (environment-sub terms) body)) body-path))

    application : ∀ {depth function argument value f a}
      → Denotes depth function f → Denotes depth argument a → E.Applies function argument value
      → ∃ λ result → Denotes depth value result × _⇝*_ sig (tm-app f a) result
    application (d-lam {body = body} {terms = terms} domain env) argument (E.a-closure body-evaluated)
      with evaluate (d∷ argument env) body-evaluated
    ... | result , denoted , path = result , denoted ,
      ⇝*-step β (O.⇝*-trans (equal-path (beta-environment _ (environment-sub terms) body)) path)
    application (d-neutral function) argument E.a-neutral = _ , d-neutral (d-app function argument) , ⇝*-refl
