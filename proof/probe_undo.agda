module probe_undo where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Core.Syntax

topSub : Term → Sub
topSub a zero = a
topSub a (suc k) = tm-var k

-- substS (topSub a) (rename wk T) ≡ T, for T with free vars < n.
-- The variable case: rename wk (var k) = var (suc k). topSub a (suc k) = var k. ✓
-- The binder case: rename wk (lam g d b) = lam g (rename wk d) (rename (ext wk) b).
--   substS (topSub a) of that = lam g (substS (topSub a) (rename wk d)) (substS (extSub (topSub a)) (rename (ext wk) b)).
--   Need: substS (extSub (topSub a)) (rename (ext wk) b) ≡ b.
--   extSub (topSub a) 0 = var 0, extSub (topSub a) (suc k) = shift 1 0 (topSub a k).
--   rename (ext wk) b has free vars ext wk j = suc (wk j) = suc (suc j)?? 
--   Hmm, ext wk 0 = 0, ext wk (suc j) = suc (wk j) = suc (suc j).
--   So rename (ext wk) (var 0) = var 0, and extSub (topSub a) 0 = var 0. ✓
--   rename (ext wk) (var (suc j)) = var (suc (suc j)), and extSub (topSub a) (suc (suc j)) = shift 1 0 (topSub a (suc j)) = shift 1 0 (var j) = var (suc j). ✗ mismatch!
--   We need var (suc (suc j)) ↦ var (suc j). So the substitution must shift down by 1 under the binder too.
