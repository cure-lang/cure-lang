------------------------------------------------------------------------
-- Reversal facts used by exact-arity CLOSED-entry branch migration.
-- These do not instantiate dependent telescope entries or erased slots.
------------------------------------------------------------------------
module Proof.FieldOrder where

open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Core.Syntax
open import Core.Signature using (IndEnv; Telescope)
open import Core.Reduction using (Signature)
open import Core.Typing using (Ctx; Conversion; _∈Tele_; ∈-here; ∈-there)
open import Proof.Progress using (FinalTerms; ft[]; ft∷)

ClosedEntries : Telescope → Set
ClosedEntries tele = ∀ {T} → T ∈Tele tele → Scoped 0 T

closed-append : ∀ xs ys → ClosedEntries xs → ClosedEntries ys → ClosedEntries (xs ++ ys)
closed-append [] ys cx cy member = cy member
closed-append ((nm , T) ∷ xs) ys cx cy ∈-here = cx ∈-here
closed-append ((nm , T) ∷ xs) ys cx cy (∈-there member) =
  closed-append xs ys (λ p → cx (∈-there p)) cy member

closed-reverse : ∀ tele → ClosedEntries tele → ClosedEntries (reverse tele)
closed-reverse [] closed ()
closed-reverse ((nm , T) ∷ tele) closed =
  subst ClosedEntries (sym (unfold-reverse (nm , T) tele))
    (closed-append (reverse tele) ((nm , T) ∷ [])
      (closed-reverse tele (λ p → closed (∈-there p)))
      (λ { ∈-here → closed ∈-here ; (∈-there ()) }))

final-append : ∀ {xs ys} → FinalTerms xs → FinalTerms ys → FinalTerms (xs ++ ys)
final-append ft[] fy = fy
final-append (ft∷ fx fxs) fy = ft∷ fx (final-append fxs fy)

final-reverse : ∀ {xs} → FinalTerms xs → FinalTerms (reverse xs)
final-reverse ft[] = ft[]
final-reverse (ft∷ {x = x} {xs = xs} fx fxs) =
  subst FinalTerms (sym (unfold-reverse x xs))
    (final-append (final-reverse fxs) (ft∷ fx ft[]))

module Spines (ind : IndEnv) (sig : Signature) (conv : Conversion) where
  open Core.Typing.Typing ind sig conv

  spine-append : ∀ {n} {Γ : Ctx n} {xs ys ts us}
    → Γ ⊢* xs ⇐* ts → Γ ⊢* ys ⇐* us → Γ ⊢* (xs ++ ys) ⇐* (ts ++ us)
  spine-append ⊢*[] q = q
  spine-append (⊢*∷ p ps) q = ⊢*∷ p (spine-append ps q)

  spine-reverse : ∀ {n} {Γ : Ctx n} {xs tele}
    → Γ ⊢* xs ⇐* tele → Γ ⊢* reverse xs ⇐* reverse tele
  spine-reverse ⊢*[] = ⊢*[]
  spine-reverse {Γ = Γ} (⊢*∷ {x = x} {xs = xs} {T = T} {tele = tele} {nm = nm} p ps) =
    subst (λ ts → Γ ⊢* reverse (x ∷ xs) ⇐* ts) (sym (unfold-reverse (nm , T) tele))
      (subst (λ ys → Γ ⊢* ys ⇐* (reverse tele ++ (nm , T) ∷ []))
        (sym (unfold-reverse x xs)) (spine-append (spine-reverse ps) (⊢*∷ p ⊢*[])))
