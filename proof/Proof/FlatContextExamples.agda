{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Actual Context/Quote artifact agreement plus native typed transport.
-- No universal Elixir/closure/NbE or quantitative usage refinement.
------------------------------------------------------------------------
module Proof.FlatContextExamples where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
import Data.Fin as Fin
import Data.Vec as V
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Core.Syntax
open import Core.Grade using (unrestricted)
open import Core.Universe using (l0; l2)
open import Core.Typing using (⟨⟩; Conversion)
open import Core.NativeRecipe using (r-leaf)
open import Core.Reduction using (⇝*-refl)
import Core.FlatContext as F
import Core.FlatContextTyping as Typed
import Core.CallerAdmission as Caller
import Core.Wire as Wire
import Core.WireConversion as C
import Proof.Progress as Final
import Proof.WireSnapshotExamples as Source
import Fixtures.ExecutableBundle as Bundle
import Fixtures.ExecutableContext as Observed
open import Proof.CheckedAdmissionExamples using (pick)
open import Core.CheckedAdmission using (present)
module R = Typed.Replay Source.Pin.admission
module Closing = Caller.Replay Source.Pin.admission

checked : R.Checked Observed.operations
checked = pick (R.verify Observed.operations) refl
frame : R.Frame
frame = R.Checked.frame checked
exact-size : R.Frame.size frame ≡ 6
exact-size = refl
exact-store : R.Frame.store frame ≡ Observed.observed
exact-store = refl
types-readback : F.quote-values 6 (F.types Observed.observed) ≡ just (F.context-types (R.Frame.context frame))
types-readback = R.Frame.types-read frame
environment-readback : F.quote-values 6 (F.environment Observed.observed) ≡ just (R.Frame.environment frame)
environment-readback = R.Frame.environment-read frame

decode-terms : ∀ {n} → V.Vec (List Char) n → Maybe (V.Vec Term n)
decode-terms V.[] = just V.[]
decode-terms (cs V.∷ rest) = C.pair V._∷_ (Wire.decode-term Bundle.table cs) (decode-terms rest)
actual-type-quote : decode-terms Observed.type-characters ≡ just (F.context-types (R.Frame.context frame))
actual-type-quote = refl
actual-environment-quote : decode-terms Observed.environment-characters ≡ just (R.Frame.environment frame)
actual-environment-quote = refl
all-native-lookups : ∀ i → F.reify 6 (V.lookup (F.types Observed.observed) i)
  ≡ just (Core.Typing.lookup (R.Frame.context frame) i)
all-native-lookups i = F.quote-complete (F.lookup-view (R.Frame.built frame) i)

fresh-index : R.Frame.substitution frame 0 ≡ tm-var 0
fresh-index = refl
literal-let-value : R.Frame.substitution frame 1 ≡ tm-atom_lit "payload"
literal-let-value = refl
dependent-let-alias : R.Frame.substitution frame 3 ≡ tm-var 4
dependent-let-alias = refl
dependent-goal : R.Frame.substitution frame 5 ≡ tm-var 5
dependent-goal = refl
not-a-neutral-identity : R.Frame.environment frame ≢ F.identity-terms 6
not-a-neutral-identity ()

alias-typed : R.N._⊢_⇒_ (R.Frame.context frame) (tm-var 3) (tm-var 5)
alias-typed = pick (R.D.at (R.Frame.context frame) (tm-var 3) (tm-var 5) r-leaf) refl
alias-transported : R.N._⊢_⇒_ (R.Frame.context frame) (tm-var 4) (tm-var 5)
alias-transported = R.Checked.transport checked alias-typed
literal-typed : R.N._⊢_⇒_ (R.Frame.context frame) (tm-var 1) tm-atom_type
literal-typed = pick (R.D.at (R.Frame.context frame) (tm-var 1) tm-atom_type r-leaf) refl
literal-transported : R.N._⊢_⇒_ (R.Frame.context frame) (tm-atom_lit "payload") tm-atom_type
literal-transported = R.Checked.transport checked literal-typed

-- Close that SAME native context through checked dependent actual terms.
caller : Caller.Request
caller = Caller.request
  (("A" , tm-type l0) ∷ ("x" , tm-var 0) ∷ ("x" , tm-var 1) ∷ ("x" , tm-var 2) ∷
    ("payload" , tm-atom_type) ∷ ("payload" , tm-atom_type) ∷ [])
  (r-leaf ∷ r-leaf ∷ r-leaf ∷ r-leaf ∷ r-leaf ∷ r-leaf ∷ [])
  (tm-atom_type ∷ tm-atom_lit "payload" ∷ tm-atom_lit "payload" ∷ tm-atom_lit "payload" ∷
    tm-atom_lit "payload" ∷ tm-atom_lit "payload" ∷ [])
  (r-leaf ∷ r-leaf ∷ r-leaf ∷ r-leaf ∷ r-leaf ∷ r-leaf ∷ [])
  (tm-var 3) (tm-var 5) r-leaf r-leaf
closed : Closing.Checked caller
closed = pick (Closing.verify caller) refl
same-native-context : R.Frame.context frame ≡ Closing.Checked.context closed
same-native-context = refl
staged-typed : R.N._⊢_⇒_ ⟨⟩ (tm-atom_lit "payload") tm-atom_type
staged-typed = Closing.T.subst⇒ (Closing.Checked.coherent closed) R.N.wf[] alias-transported
staged-safe : R.C.Sound.SafeState (tm-atom_lit "payload") tm-atom_type
staged-safe = R.C.Sound.trace-safe
  (R.N.⇐-infer staged-typed (Conversion.≈-refl R.C.W.M.conversion {t = tm-atom_type}))
  Final.f-atom_lit ⇝*-refl

-- The generic opaque-only theorem holds, but does not apply to lets.
opaque-two : F.Built
  (F.extend-opaque (F.extend-opaque (F.empty tt) (F.sort l0) unrestricted) (F.neutral 0) unrestricted)
  (Core.Typing.extend (Core.Typing.extend ⟨⟩ (tm-type l0)) (tm-var 0))
opaque-two = F.b-opaque (F.b-opaque F.b-empty F.q-sort unrestricted)
  (F.q-neutral (s≤s z≤n)) unrestricted
opaque-identity : F.environment-terms opaque-two ≡ F.identity-terms 2
opaque-identity = F.opaque-identity opaque-two tt
opaque-indices : ∀ i → V.lookup (F.environment-terms opaque-two) i ≡ tm-var (Fin.toℕ i)
opaque-indices = F.identity-lookup 2

escaped-level : F.reify 1 (F.neutral 1) ≡ nothing
escaped-level = refl
zero-depth-level : F.reify 0 (F.neutral 0) ≡ nothing
zero-depth-level = refl
bad-kind : present (R.verify (Typed.bind-opaque (F.sort l2) unrestricted ∷ [])) ≡ false
bad-kind = refl
bad-definition : present (R.verify (Typed.bind-defined F.atom-type (F.sort l0) ∷ [])) ≡ false
bad-definition = refl
escaped-definition : present
  (R.verify (Typed.bind-defined F.atom-type (F.neutral 0) ∷ [])) ≡ false
escaped-definition = refl

-- A merely scoped invented neutral at a defined slot is not a valid
-- let-transparent substitution. Construction/kinds pass, images fail.
invented-let-neutral : List Typed.Operation
invented-let-neutral =
  Typed.bind-defined (F.sort l0) F.atom-type ∷ Typed.bind-opaque (F.neutral 0) unrestricted ∷ []
shape-and-kinds-pass : present (R.build invented-let-neutral) ≡ true
shape-and-kinds-pass = refl
invented-frame : R.Frame
invented-frame = pick (R.build invented-let-neutral) shape-and-kinds-pass
coherence-rejects-invented-neutral : present (R.images invented-frame) ≡ false
coherence-rejects-invented-neutral = refl
invented-context-rejected : present (R.verify invented-let-neutral) ≡ false
invented-context-rejected = refl
