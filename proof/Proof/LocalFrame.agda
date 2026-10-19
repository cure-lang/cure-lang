------------------------------------------------------------------------
-- Stability of LOCAL declaration instantiation. The scope premise is
-- essential: declaration variables refer to preceding fields/parameters,
-- not to the unrelated ambient typing context.
------------------------------------------------------------------------
module Proof.LocalFrame where

open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong)
open import Core.Syntax
open import Core.LocalFrame
open import Proof.Substitution
  using (rename-prefix; subst-prefix; rename-scoped; substS-scoped;
         ext^-fix; extSub^-fix)

rename-local : ∀ {locals ty} → Scoped (length locals) ty → ∀ ρ
  → rename ρ (instantiatePrefix locals ty)
    ≡ instantiatePrefix (renameTerms ρ locals) ty
rename-local {locals} {ty} scoped ρ =
  trans (rename-prefix ρ locals ty)
    (cong (instantiatePrefix (renameTerms ρ locals))
      (rename-scoped scoped (ext^-fix (length locals) ρ)))

subst-local : ∀ {locals ty} → Scoped (length locals) ty → ∀ σ
  → substS σ (instantiatePrefix locals ty)
    ≡ instantiatePrefix (substTermsS σ locals) ty
subst-local {locals} {ty} scoped σ =
  trans (subst-prefix σ locals ty)
    (cong (instantiatePrefix (substTermsS σ locals))
      (substS-scoped scoped (extSub^-fix (length locals) σ)))
