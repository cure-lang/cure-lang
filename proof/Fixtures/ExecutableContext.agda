{-# OPTIONS --guardedness #-}
-- Generated from actual Context/Quote observations; bounded artifact only.
module Fixtures.ExecutableContext where
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.String.Base using (toList)
open import Core.Grade using (erased; linear; affine; unrestricted)
open import Core.Universe using (l0; l1; l2)
open import Core.FlatContext
open import Core.FlatContextTyping using (Operation; bind-opaque; bind-defined)
import Fixtures.ExecutableSnapshot as Source

operations : List Operation
operations = ((bind-opaque (sort l0) unrestricted) ∷ (bind-opaque (neutral 0) linear) ∷ (bind-defined (neutral 0) (neutral 1)) ∷ (bind-opaque (neutral 0) affine) ∷ (bind-defined atom-type (atom "payload")) ∷ (bind-opaque atom-type erased) ∷ [])
observed : Store Source.source 6
observed = store (atom-type ∷ atom-type ∷ (neutral 0) ∷ (neutral 0) ∷ (neutral 0) ∷ (sort l0) ∷ []) (erased ∷ unrestricted ∷ affine ∷ unrestricted ∷ linear ∷ unrestricted ∷ []) ((neutral 5) ∷ (atom "payload") ∷ (neutral 3) ∷ (neutral 1) ∷ (neutral 1) ∷ (neutral 0) ∷ [])
type-characters : Vec (List Char) 6
type-characters = (toList "(111111111111111111;;;)" ∷ toList "(111111111111111111;;;)" ∷ toList "(1;;11111;)" ∷ toList "(1;;11111;)" ∷ toList "(1;;11111;)" ∷ toList "(;;;)" ∷ [])
environment-characters : Vec (List Char) 6
environment-characters = (toList "(1;;;)" ∷ toList "(1111111111111111111;1111;;)" ∷ toList "(1;;11;)" ∷ toList "(1;;1111;)" ∷ toList "(1;;1111;)" ∷ toList "(1;;11111;)" ∷ [])
