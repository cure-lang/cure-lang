------------------------------------------------------------------------
-- Confluence of the UNCHANGED Core small-step relation.
--
-- The former wide-parallel local-join recursion was unchecked. The proof
-- now factors through genuinely one-step strict parallel reduction:
-- one-step substitution -> strong diamond -> checked strip/closure.
-- Core.Parallel supplies only its independently checked simulation.
-- No termination override or new axiom is used. This is a specification
-- theorem with closed global bodies, not executable kernel refinement.
------------------------------------------------------------------------
module Proof.Confluence where

open import Data.Maybe using (just)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core.Syntax using (Scoped)
open import Core.Reduction using (Signature)
import Proof.StrictConfluence as Strict

ClosedBody : Signature → Set
ClosedBody sig = ∀ {f body′} → Signature.body sig f ≡ just body′ → Scoped 0 body′

module Conf (sig : Signature) (cb : ClosedBody sig) where
  open Strict.Laws sig (λ {f} {b} found → cb {f = f} {body′ = b} found) public
  open O public

  -- Compatibility results for the wide relation, derived AFTER checked
  -- confluence. Local joinability is never used as a closure assumption.
  ⇉-confluent : ∀ {t u v} → t ⇉* u → t ⇉* v
    → ∃ λ w → u ⇉* w × v ⇉* w
  ⇉-confluent p q with confluence (⇉→⇝*-star p) (⇉→⇝*-star q)
  ... | w , uw , vw = w , ⇝→⇉* uw , ⇝→⇉* vw

  ⇉-diamond-star : ∀ {t u v} → t ⇉* u → t ⇉* v
    → ∃ λ w → u ⇉* w × v ⇉* w
  ⇉-diamond-star = ⇉-confluent

  ⇉-diamond : ∀ {t u v} → t ⇉ u → t ⇉ v
    → ∃ λ w → u ⇉* w × v ⇉* w
  ⇉-diamond p q = ⇉-confluent (⇉*-step p ⇉*-refl) (⇉*-step q ⇉*-refl)
