------------------------------------------------------------------------
-- Sufficient residual-form grammar for the supported syntax slice.
-- Not scope, typing, layout, normalization or conversion completeness.
-- Opaque globals are checked against the ACTUAL native signature.
------------------------------------------------------------------------
module Core.ResidualNormal where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core.Syntax
open import Core.Reduction using (Signature)

mutual
  data Normal (sig : Signature) : Term → Set where
    nf-type : ∀ {l} → Normal sig (tm-type l)
    nf-atom-type : Normal sig tm-atom_type
    nf-atom : ∀ {name} → Normal sig (tm-atom_lit name)
    nf-pi : ∀ {g d b} → Normal sig d → Normal sig b → Normal sig (tm-pi g d b)
    nf-lam : ∀ {g d b} → Normal sig d → Normal sig b → Normal sig (tm-lam g d b)
    nf-data : ∀ {name ps is} → Normals sig ps → Normals sig is → Normal sig (tm-data name ps is)
    nf-ctor : ∀ {name args} → Normals sig args → Normal sig (tm-ctor name args)
    nf-neutral : ∀ {term} → Residual sig term → Normal sig term
  data Residual (sig : Signature) : Term → Set where
    ne-var : ∀ {k} → Residual sig (tm-var k)
    ne-global : ∀ {name} → Signature.body sig name ≡ nothing → Residual sig (tm-global name)
    ne-app : ∀ {f a} → Residual sig f → Normal sig a → Residual sig (tm-app f a)
    ne-case : ∀ {s m branches} → Residual sig s → Normal sig m → Branches sig branches
      → Residual sig (tm-case s m branches)
  data Normals (sig : Signature) : List Term → Set where
    nf[] : Normals sig []
    nf∷ : ∀ {t ts} → Normal sig t → Normals sig ts → Normals sig (t ∷ ts)
  data Branches (sig : Signature) : List Branch → Set where
    nb[] : Branches sig []
    nb∷ : ∀ {name ar body rest} → Normal sig body → Branches sig rest
      → Branches sig ((name , ar , body) ∷ rest)

mutual
  check : (sig : Signature) (term : Term) → Maybe (Normal sig term)
  check sig (tm-type l) = just nf-type
  check sig tm-atom_type = just nf-atom-type
  check sig (tm-atom_lit name) = just nf-atom
  check sig (tm-pi g d b) with check sig d | check sig b
  ... | just domain | just body = just (nf-pi domain body)
  ... | _ | _ = nothing
  check sig (tm-lam g d b) with check sig d | check sig b
  ... | just domain | just body = just (nf-lam domain body)
  ... | _ | _ = nothing
  check sig (tm-data name ps is) with check-terms sig ps | check-terms sig is
  ... | just params | just indices = just (nf-data params indices)
  ... | _ | _ = nothing
  check sig (tm-ctor name args) with check-terms sig args
  ... | just fields = just (nf-ctor fields)
  ... | nothing = nothing
  check sig other with check-neutral sig other
  ... | just residual = just (nf-neutral residual)
  ... | nothing = nothing

  check-neutral : (sig : Signature) (term : Term) → Maybe (Residual sig term)
  check-neutral sig (tm-var k) = just ne-var
  check-neutral sig (tm-global name) with Signature.body sig name in found
  ... | nothing = just (ne-global found)
  ... | just body = nothing
  check-neutral sig (tm-app f a) with check-neutral sig f | check sig a
  ... | just function | just argument = just (ne-app function argument)
  ... | _ | _ = nothing
  check-neutral sig (tm-case s m branches)
    with check-neutral sig s | check sig m | check-branches sig branches
  ... | just scrutinee | just motive | just bodies = just (ne-case scrutinee motive bodies)
  ... | _ | _ | _ = nothing
  check-neutral sig other = nothing

  check-terms : (sig : Signature) (terms : List Term) → Maybe (Normals sig terms)
  check-terms sig [] = just nf[]
  check-terms sig (t ∷ ts) with check sig t | check-terms sig ts
  ... | just head | just tail = just (nf∷ head tail)
  ... | _ | _ = nothing
  check-branches : (sig : Signature) (branches : List Branch) → Maybe (Branches sig branches)
  check-branches sig [] = just nb[]
  check-branches sig ((name , ar , body) ∷ rest) with check sig body | check-branches sig rest
  ... | just head | just tail = just (nb∷ head tail)
  ... | _ | _ = nothing
