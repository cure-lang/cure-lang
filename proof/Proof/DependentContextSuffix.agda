------------------------------------------------------------------------
-- Pure context suffix foundations for native mutual transport.
-- All typing evidence belongs to ONE native ind/sig/conv instance.
-- No transport theorem or well-formedness callback is assumed.
------------------------------------------------------------------------
module Proof.DependentContextSuffix where

open import Data.Nat using (ℕ; zero; suc; pred; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Core.Syntax
open import Core.Signature using (IndEnv; Telescope)
open import Core.Reduction using (Signature)
open import Core.Universe using (Level)
open import Core.Typing using (Ctx; ⟨⟩; _▷_; renameCtx; extend; Conversion)
open import Core.DependentTyping using (Opened; op[]; op∷)
import Core.DependentTyping as Native
open import Proof.Substitution
  using (rename-id; renameSub; rename-subst; substCompose; subst-compose;
         subst-extSub-wk)

-- These retractions apply to arbitrary raw terms/contexts: scoping is
-- unnecessary because pred is a left inverse to wk at EVERY index.
unweaken-term : ∀ T → rename pred (rename wk T) ≡ T
unweaken-term T = trans (rename-compose pred wk T) (rename-id T)

unweaken-context : ∀ {n} (Γ : Ctx n)
  → renameCtx pred (renameCtx wk Γ) ≡ Γ
unweaken-context ⟨⟩ = refl
unweaken-context (Γ ▷ T) =
  cong₂ _▷_ (unweaken-context Γ) (unweaken-term T)

weaken-term-injective : ∀ {T U} → rename wk T ≡ rename wk U → T ≡ U
weaken-term-injective {T} {U} eq =
  trans (sym (unweaken-term T)) (trans (cong (rename pred) eq) (unweaken-term U))

weaken-context-injective : ∀ {n} {Γ Δ : Ctx n}
  → renameCtx wk Γ ≡ renameCtx wk Δ → Γ ≡ Δ
weaken-context-injective {Γ = Γ} {Δ = Δ} eq =
  trans (sym (unweaken-context Γ))
    (trans (cong (renameCtx pred) eq) (unweaken-context Δ))

snoc-injective : ∀ {n} {Γ Δ : Ctx n} {T U}
  → (Γ ▷ T) ≡ (Δ ▷ U) → Γ ≡ Δ × T ≡ U
snoc-injective refl = refl , refl

extend-injective : ∀ {n} {Γ Δ : Ctx n} {T U}
  → extend Γ T ≡ extend Δ U → Γ ≡ Δ × T ≡ U
extend-injective eq =
  weaken-context-injective (proj₁ (snoc-injective eq)) ,
  weaken-term-injective (proj₂ (snoc-injective eq))

AnyCtx : Set
AnyCtx = Σ ℕ Ctx

unextend : AnyCtx → AnyCtx
unextend (zero , ⟨⟩) = zero , ⟨⟩
unextend (suc n , Γ ▷ T) = n , renameCtx pred Γ

unextend-extend : ∀ {n} (Γ : Ctx n) T
  → unextend (suc n , extend Γ T) ≡ (n , Γ)
unextend-extend Γ T = cong (_ ,_) (unweaken-context Γ)

opened-length : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ tele}
  → Opened Γ σ tele Θ → length tele + n ≡ m
opened-length op[] = refl
opened-length {n = n} (op∷ {tele = tele} rest) =
  trans (sym (+-suc (length tele) n)) (opened-length rest)
extSub-suc : ∀ k σ → extSub^ k (extSub σ) ≡ extSub^ (suc k) σ
extSub-suc zero σ = refl
extSub-suc (suc k) σ = cong extSub (extSub-suc k σ)

-- The rightmost fresh field is the last native WF constructor. Unlike
-- extendTele, this diagram preserves declaration order and specialises
-- each field under all PRECEDING fresh fields.
data OpenedSnoc {n} (Γ : Ctx n) (σ : Sub)
  : Telescope → ∀ {m} → Ctx m → Set where
  os[] : OpenedSnoc Γ σ [] Γ
  os∷ : ∀ {m} {Θ : Ctx m} {tele name T}
    → OpenedSnoc Γ σ tele Θ
    → OpenedSnoc Γ σ (tele ++ ((name , T) ∷ []))
        (extend Θ (substS (extSub^ (length tele) σ) T))

prepend-snoc : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ tele name T}
  → OpenedSnoc (extend Γ (substS σ T)) (extSub σ) tele Θ
  → OpenedSnoc Γ σ ((name , T) ∷ tele) Θ
prepend-snoc os[] = os∷ os[]
prepend-snoc {Γ = Γ} {σ = σ} {name = name} {T = T}
  (os∷ {Θ = Θ} {tele = tele} {name = last} {T = U} rest) =
  subst (λ A → OpenedSnoc Γ σ (((name , T) ∷ tele) ++ ((last , U) ∷ []))
      (extend Θ A))
    (cong (λ τ → substS τ U) (sym (extSub-suc (length tele) σ)))
    (os∷ (prepend-snoc rest))

opened-snoc : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ tele}
  → Opened Γ σ tele Θ → OpenedSnoc Γ σ tele Θ
opened-snoc op[] = os[]
opened-snoc (op∷ rest) = prepend-snoc (opened-snoc rest)

append-one : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ tele}
  → Opened Γ σ tele Θ → ∀ name T
  → Opened Γ σ (tele ++ ((name , T) ∷ []))
      (extend Θ (substS (extSub^ (length tele) σ) T))
append-one op[] name T = op∷ op[]
append-one {Γ = Γ} {σ = σ} (op∷ {name = first} {T = U} {tele = tele} rest) name T =
  subst (λ A → Opened Γ σ (((first , U) ∷ tele) ++ ((name , T) ∷ []))
      (extend _ A))
    (cong (λ τ → substS τ T) (extSub-suc (length tele) σ))
    (op∷ (append-one rest name T))

snoc-opened : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ tele}
  → OpenedSnoc Γ σ tele Θ → Opened Γ σ tele Θ
snoc-opened os[] = op[]
snoc-opened (os∷ {name = name} {T = T} rest) =
  append-one (snoc-opened rest) name T

-- Exact squares for a declaration opened under k preceding fresh fields.
-- The ENTIRE substitution is mapped, so no declaration scope is needed.
rename-opening-index : ∀ k ρ σ i
  → rename (ext^ k ρ) (extSub^ k σ i)
      ≡ extSub^ k (renameSub ρ σ) i
rename-opening-index zero ρ σ i = refl
rename-opening-index (suc k) ρ σ zero = refl
rename-opening-index (suc k) ρ σ (suc i) =
  trans (sym (ext-wk-rename (ext^ k ρ) (extSub^ k σ i)))
    (cong (rename wk) (rename-opening-index k ρ σ i))

subst-opening-index : ∀ k τ σ i
  → substS (extSub^ k τ) (extSub^ k σ i)
      ≡ extSub^ k (substCompose τ σ) i
subst-opening-index zero τ σ i = refl
subst-opening-index (suc k) τ σ zero = refl
subst-opening-index (suc k) τ σ (suc i) =
  trans (subst-extSub-wk (extSub^ k τ) (extSub^ k σ i))
    (cong (rename wk) (subst-opening-index k τ σ i))

rename-opening-square : ∀ k ρ σ T
  → rename (ext^ k ρ) (substS (extSub^ k σ) T)
      ≡ substS (extSub^ k (renameSub ρ σ)) T
rename-opening-square k ρ σ T =
  trans (rename-subst (ext^ k ρ) (extSub^ k σ) T)
    (cong (λ τ → substS τ T) (funext (rename-opening-index k ρ σ)))

subst-opening-square : ∀ k τ σ T
  → substS (extSub^ k τ) (substS (extSub^ k σ) T)
      ≡ substS (extSub^ k (substCompose τ σ)) T
subst-opening-square k τ σ T =
  trans (subst-compose (extSub^ k τ) (extSub^ k σ) T)
    (cong (λ υ → substS υ T) (funext (subst-opening-index k τ σ)))

append-renamed : ∀ {n m} {Δ : Ctx n} {Ω : Ctx m} {ρ σ tele}
  → Opened Δ (renameSub ρ σ) tele Ω → ∀ name T
  → Opened Δ (renameSub ρ σ) (tele ++ ((name , T) ∷ []))
      (extend Ω (rename (ext^ (length tele) ρ)
        (substS (extSub^ (length tele) σ) T)))
append-renamed {Δ = Δ} {Ω = Ω} {ρ = ρ} {σ = σ} {tele = tele} opening name T =
  subst (λ A → Opened Δ (renameSub ρ σ) (tele ++ ((name , T) ∷ [])) (extend Ω A))
    (sym (rename-opening-square (length tele) ρ σ T))
    (append-one opening name T)

append-substituted : ∀ {n m} {Δ : Ctx n} {Ω : Ctx m} {τ σ tele}
  → Opened Δ (substCompose τ σ) tele Ω → ∀ name T
  → Opened Δ (substCompose τ σ) (tele ++ ((name , T) ∷ []))
      (extend Ω (substS (extSub^ (length tele) τ)
        (substS (extSub^ (length tele) σ) T)))
append-substituted {Δ = Δ} {Ω = Ω} {τ = τ} {σ = σ} {tele = tele} opening name T =
  subst (λ A → Opened Δ (substCompose τ σ) (tele ++ ((name , T) ∷ [])) (extend Ω A))
    (sym (subst-opening-square (length tele) τ σ T))
    (append-one opening name T)

module ContextSuffix (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Native.Typing ind sig conv

  data AnyWF : Set where
    wctx : ∀ {n} {Γ : Ctx n} → WellFormed Γ → AnyWF

  context : AnyWF → AnyCtx
  context (wctx {n} {Γ} wf) = n , Γ

  evidence : (w : AnyWF) → WellFormed (proj₂ (context w))
  evidence (wctx wf) = wf

  dropOne : AnyWF → AnyWF
  dropOne (wctx wf[]) = wctx wf[]
  dropOne (wctx (wf∷ wf scope kind)) = wctx wf

  context-dropOne : ∀ w → context (dropOne w) ≡ unextend (context w)
  context-dropOne (wctx wf[]) = refl
  context-dropOne (wctx (wf∷ {Γ = Γ} {T = T} wf scope kind)) =
    sym (unextend-extend Γ T)

  drop : ℕ → AnyWF → AnyWF
  drop zero w = w
  drop (suc k) w = dropOne (drop k w)

  drop-compose : ∀ j k w → drop (j + k) w ≡ drop j (drop k w)
  drop-compose zero k w = refl
  drop-compose (suc j) k w = cong dropOne (drop-compose j k w)

  drop-one : ∀ k w → drop (suc k) w ≡ drop k (dropOne w)
  drop-one zero w = refl
  drop-one (suc k) w = cong dropOne (drop-one k w)

  drop-opened : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ tele}
    → Opened Γ σ tele Θ → (wf : WellFormed Θ)
    → context (drop (length tele) (wctx wf)) ≡ (n , Γ)
  drop-opened op[] wf = refl
  drop-opened {Γ = Γ} {σ = σ} (op∷ {T = T} {tele = tele} rest) wf =
    trans (context-dropOne (drop (length tele) (wctx wf)))
      (trans (cong unextend (drop-opened rest wf))
        (unextend-extend Γ (substS σ T)))

  cast-WF : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m}
    → (n , Γ) ≡ (m , Θ) → WellFormed Γ → WellFormed Θ
  cast-WF refl wf = wf

  prefix-WF : ∀ {n m} {Γ : Ctx n} {Θ : Ctx m} {σ tele}
    → Opened Γ σ tele Θ → WellFormed Θ → WellFormed Γ
  prefix-WF {tele = tele} opening wf =
    cast-WF (drop-opened opening wf) (evidence (drop (length tele) (wctx wf)))

  -- A view of the ACTUAL native last WF constructor. The scoped/kind
  -- witnesses and preceding WF are not reconstructed by transport.
  record LastWF {n} (Θ : Ctx (suc n)) : Set where
    field
      prefix : Ctx n
      type : Term
      level : Level
      previous : WellFormed prefix
      scoped : Scoped n type
      kind : prefix ⊢ type ⇒ tm-type level
      shape : Θ ≡ extend prefix type

  last-WF : ∀ {n} {Θ : Ctx (suc n)} → WellFormed Θ → LastWF Θ
  last-WF (wf∷ {Γ = Γ} {T = T} {l = l} wf scope kind) = record
    { prefix = Γ ; type = T ; level = l ; previous = wf
    ; scoped = scope ; kind = kind ; shape = refl }

  wf-prefix : ∀ {n} {Γ : Ctx n} {T}
    → WellFormed (extend Γ T) → WellFormed Γ
  wf-prefix wf = subst WellFormed
    (sym (proj₁ (extend-injective (LastWF.shape (last-WF wf)))))
    (LastWF.previous (last-WF wf))
