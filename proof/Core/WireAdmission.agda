{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Both source and certificate arrive as characters. A supplied name
-- table remains explicit, not authenticated by character parsing.
------------------------------------------------------------------------
module Core.WireAdmission where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Core.Syntax using (Name)
open import Core.Signature using (just-inj)
import Core.ExecutableSnapshot as I
import Core.WireSnapshot as Source
import Core.CheckedAdmission as P
open P using (present)

record Checked (table : List Name) (source-chars certificate-chars : List Char) : Set where
  field
    source : I.Input
    decoded : Source.decode table source-chars ≡ just source
    admission : P.Checked source table certificate-chars
    verified : P.verify source table certificate-chars ≡ just admission
  module C = P.Checked admission
  module Bodies = P.Bodies admission

package : ∀ table source-chars certificate-chars source
  → Source.decode table source-chars ≡ just source
  → (result : Maybe (P.Checked source table certificate-chars))
  → P.verify source table certificate-chars ≡ result
  → Maybe (Checked table source-chars certificate-chars)
package table source-chars certificate-chars source decoded nothing verified = nothing
package table source-chars certificate-chars source decoded (just admission) verified = just record
  { source = source ; decoded = decoded ; admission = admission ; verified = verified }
finish : ∀ table source-chars certificate-chars source
  → Source.decode table source-chars ≡ just source → Maybe (Checked table source-chars certificate-chars)
finish table source-chars certificate-chars source decoded = package table source-chars certificate-chars
  source decoded (P.verify source table certificate-chars) refl
package-status : ∀ table source-chars certificate-chars source decoded result verified
  → present (package table source-chars certificate-chars source decoded result verified) ≡ present result
package-status table source-chars certificate-chars source decoded nothing verified = refl
package-status table source-chars certificate-chars source decoded (just admission) verified = refl
finish-status : ∀ table source-chars certificate-chars source decoded
  → present (finish table source-chars certificate-chars source decoded)
    ≡ present (P.verify source table certificate-chars)
finish-status table source-chars certificate-chars source decoded =
  package-status table source-chars certificate-chars source decoded (P.verify source table certificate-chars) refl

dispatch : ∀ table source-chars certificate-chars (result : Maybe I.Input)
  → Source.decode table source-chars ≡ result → Maybe (Checked table source-chars certificate-chars)
dispatch table source-chars certificate-chars nothing decoded = nothing
dispatch table source-chars certificate-chars (just source) decoded =
  finish table source-chars certificate-chars source decoded
verify : ∀ table source-chars certificate-chars → Maybe (Checked table source-chars certificate-chars)
verify table source-chars certificate-chars =
  dispatch table source-chars certificate-chars (Source.decode table source-chars) refl
dispatch-status : ∀ table source-chars certificate-chars result decoded source → result ≡ just source
  → present (dispatch table source-chars certificate-chars result decoded)
    ≡ present (P.verify source table certificate-chars)
dispatch-status table source-chars certificate-chars nothing decoded source ()
dispatch-status table source-chars certificate-chars (just source) decoded .source refl =
  finish-status table source-chars certificate-chars source decoded
verify-decoded : ∀ table source-chars certificate-chars source
  → Source.decode table source-chars ≡ just source
  → present (verify table source-chars certificate-chars) ≡ present (P.verify source table certificate-chars)
verify-decoded table source-chars certificate-chars source decoded =
  dispatch-status table source-chars certificate-chars (Source.decode table source-chars) refl source decoded

-- A known source is identified by actual decoder equality, not by a
-- callback or proof-irrelevance assumption. Useful for concrete goals.
module Pin {table source-chars certificate-chars}
  (checked : Checked table source-chars certificate-chars)
  (expected : I.Input) (decoded : Source.decode table source-chars ≡ just expected) where
  source-equal : Checked.source checked ≡ expected
  source-equal = just-inj (trans (sym (Checked.decoded checked)) decoded)
  admission : P.Checked expected table certificate-chars
  admission = subst (λ source → P.Checked source table certificate-chars) source-equal (Checked.admission checked)
  module C = P.Checked admission
  module Bodies = P.Bodies admission
