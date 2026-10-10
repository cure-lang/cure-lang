module probe_ren where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax

-- A renaming: maps each de Bruijn index in the source to an index in the target.
Ren : Set
Ren = ℕ → ℕ

-- Extend a renaming under a binder (the new binder maps to itself, others shift).
ext : Ren → Ren
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

-- Apply a renaming to a variable.
-- Apply a renaming to a term: rename every free variable.
-- This is the standard "weakening by renaming" for de Bruijn.
