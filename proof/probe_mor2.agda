module probe_mor2 where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Typing using (Context; _∋_at_; here; there; extend)

-- Weakening: insert a fresh binder at the FRONT, renaming = suc.
-- Source: Γ. Target: S ∷ renameCtx suc Γ.
-- The lookup lemma: Γ ∋ T at k → (S ∷ renameCtx suc Γ) ∋ rename suc T at suc k.
wk : Ren
wk k = suc k

wk-mor : ∀ {Γ T k} (S : Term) → Γ ∋ T at k → (S ∷ map (rename wk) Γ) ∋ rename wk T at wk k
wk-mor S here = there here
wk-mor S (there p) = there (wk-mor _ p)

-- Now the key: under a binder, the source becomes T ∷ Γ, and we need to
-- weaken T ∷ Γ. The target should be S ∷ renameCtx wk (T ∷ Γ) = S ∷ rename wk T ∷ renameCtx wk Γ.
-- But the fundamental lemma's binder case needs the target to be
-- renameCtx (ext wk) (T ∷ Γ) = rename (ext wk) T ∷ renameCtx (ext wk) Γ.
-- These differ. So we need the fundamental lemma stated over an ARBITRARY
-- morphism whose target is recursively built.
