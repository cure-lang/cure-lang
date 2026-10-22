{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Source + name table + certificate characters -> checked native safety.
-- Metadata, ALL raw payloads, conversion and native evidence are derived.
-- Not Elixir extraction/acceptance, semantic totality or runtime refinement.
------------------------------------------------------------------------
module Core.CheckedAdmission where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.String.Properties as String
open import Core.Syntax using (Name; Term)
open import Core.Typing using (⟨⟩)
open import Core.Reduction using (_⇝*_)
import Core.CanonicalSnapshot as S
import Core.ExecutableSnapshot as I
import Core.ExecutableReplay as Payloads
import Core.Wire as Wire
import Core.WireCertificate as Codec
import Proof.Confluence as Confluence
import Proof.ReductionConversion as Reduction
import Proof.DependentDataConversion as Components
import Proof.DependentLiteralPreservation as Layouts
import Proof.DependentSoundness as Safety

present : ∀ {A : Set} → Maybe A → Bool
present nothing = false
present (just value) = true

-- One definition fixes dependent model identities; no proof irrelevance
-- is assumed between independently reconstructed metadata/payload proofs.
module World (source : I.Input) (metadata : I.Accepted source)
  (payloads : Payloads.Replay.Payloads source metadata) where
  module R = Payloads.Replay source metadata
  snapshot = R.snapshot
  ind = S.Snapshot.ind snapshot
  sig = S.Snapshot.sig snapshot
  closed : Confluence.ClosedBody sig
  closed {f} {b} found = R.bodies-closed payloads {name = f} found
  module M = Reduction.Model sig closed
  module D = Components.Model sig closed
  module Replay = Codec.Replay source metadata payloads M.conversion
    (λ {t} {u} → M.reduce-converts {t = t} {u = u})
  module G = Replay.G
  module N = G.C.N

record Checked (source : I.Input) (table : List Name) (characters : List Char) : Set where
  field
    metadata : I.Accepted source
    payloads : Payloads.Replay.Payloads source metadata
    recipes : Codec.Envelope
    decoded : Codec.decode table characters ≡ just recipes
  module W = World source metadata payloads
  field
    evidence : W.G.C.Evidence
    replayed : W.G.certificate (Codec.Envelope.families recipes) (Codec.Envelope.packets recipes)
      ≡ just evidence
  character-result : W.Replay.checked table characters ≡ just evidence
  character-result rewrite decoded = replayed
  valid : W.N.SignatureValid
  valid = W.G.C.validity evidence
  specification : Safety.Specification W.ind W.sig W.M.conversion
  specification = record
    { signature-valid = valid
    ; data-components = W.D.data-components
    ; reduction-converts = λ {t} {u} → W.M.reduce-converts {t = t} {u = u}
    ; global-bodies-final = λ {name} → W.R.bodies-final payloads {name}
    ; builtin-shapes = Layouts.no-builtins W.ind (λ key → refl) }
  module Sound = Safety.Sound W.ind W.sig W.M.conversion specification

  eligible : ∀ {entry body} → entry ∈ I.Input.globals source
    → I.GlobalInput.body entry ≡ just body
    → W.G.C.A.Eligible ⟨⟩ body (I.GlobalInput.type entry)
  eligible = W.G.C.eligible evidence

-- Lookup selects actual source members; no lookup-typing witness is input.
record Selected (entries : List I.GlobalInput) (name : Name) : Set where
  constructor selected
  field
    entry : I.GlobalInput
    member : entry ∈ entries
    same-name : I.GlobalInput.name entry ≡ name
select : (entries : List I.GlobalInput) (name : Name) → Maybe (Selected entries name)
select [] name = nothing
select (entry ∷ entries) name with String._≟_ (I.GlobalInput.name entry) name
... | yes same = just (selected entry (here refl) same)
... | no different with select entries name
... | nothing = nothing
... | just (selected chosen member same) = just (selected chosen (there member) same)

module Bodies {source table characters} (checked : Checked source table characters) where
  module C = Checked checked
  record Body (name : Name) : Set where
    field
      selection : Selected (I.Input.globals source) name
      term : Term
      found : I.GlobalInput.body (Selected.entry selection) ≡ just term
    goal : Term
    goal = I.GlobalInput.type (Selected.entry selection)
    admitted : C.W.N.Admitted ⟨⟩ term goal
    admitted = C.W.G.C.admitted C.evidence (Selected.member selection) found
    eligible : C.W.G.C.A.Eligible ⟨⟩ term goal
    eligible = C.eligible (Selected.member selection) found
    trace-safe : ∀ {endpoint} → _⇝*_ C.W.sig term endpoint → C.Sound.SafeState endpoint goal
    trace-safe = C.Sound.trace-safe (C.W.G.C.A.Eligible.checked eligible)
      (C.W.G.C.A.Eligible.source-final eligible)
    run : ℕ → C.Sound.FuelResult term goal
    run fuel = C.Sound.soundness-fuel fuel (C.W.G.C.A.Eligible.checked eligible)
      (C.W.G.C.A.Eligible.source-final eligible)
    tree : C.Sound.EvalTree term goal
    tree = C.Sound.soundness-tree (C.W.G.C.A.Eligible.checked eligible)
      (C.W.G.C.A.Eligible.source-final eligible)
    budgets-agree : ∀ fuel → run fuel ≡ C.Sound.truncate fuel tree
    budgets-agree fuel = C.Sound.soundness-fuel≡truncate fuel
      (C.W.G.C.A.Eligible.checked eligible) (C.W.G.C.A.Eligible.source-final eligible)

  admit : (name : Name) → Maybe (Body name)
  admit name with select (I.Input.globals source) name
  ... | nothing = nothing
  ... | just chosen with I.GlobalInput.body (Selected.entry chosen) in found
  ... | nothing = nothing
  ... | just body = just record { selection = chosen ; term = body ; found = found }

module Finish (source : I.Input) (metadata : I.Accepted source)
  (payloads : Payloads.Replay.Payloads source metadata) where
  module W = World source metadata payloads
  package : ∀ table characters recipes → Codec.decode table characters ≡ just recipes
    → (result : Maybe W.G.C.Evidence)
    → W.G.certificate (Codec.Envelope.families recipes) (Codec.Envelope.packets recipes) ≡ result
    → Maybe (Checked source table characters)
  package table characters recipes decoded nothing replayed = nothing
  package table characters recipes decoded (just evidence) replayed = just record
    { metadata = metadata ; payloads = payloads ; recipes = recipes ; decoded = decoded
    ; evidence = evidence ; replayed = replayed }
  finish : ∀ table characters recipes → Codec.decode table characters ≡ just recipes
    → Maybe (Checked source table characters)
  finish table characters recipes decoded = package table characters recipes decoded
    (W.G.certificate (Codec.Envelope.families recipes) (Codec.Envelope.packets recipes)) refl
  package-status : ∀ table characters recipes decoded result replayed
    → present (package table characters recipes decoded result replayed) ≡ present result
  package-status table characters recipes decoded nothing replayed = refl
  package-status table characters recipes decoded (just evidence) replayed = refl
  finish-status : ∀ table characters recipes decoded
    → present (finish table characters recipes decoded)
      ≡ present (W.G.certificate (Codec.Envelope.families recipes) (Codec.Envelope.packets recipes))
  finish-status table characters recipes decoded = package-status table characters recipes decoded
    (W.G.certificate (Codec.Envelope.families recipes) (Codec.Envelope.packets recipes)) refl

check-data : ∀ source table characters recipes → Codec.decode table characters ≡ just recipes
  → Maybe (Checked source table characters)
check-data source table characters recipes decoded with I.check source
... | no rejected = nothing
... | yes metadata with Payloads.Replay.check source metadata
... | no rejected = nothing
... | yes payloads = Finish.finish source metadata payloads table characters recipes decoded

dispatch : ∀ source table characters (result : Maybe Codec.Envelope)
  → Codec.decode table characters ≡ result → Maybe (Checked source table characters)
dispatch source table characters nothing decoded = nothing
dispatch source table characters (just recipes) decoded = check-data source table characters recipes decoded
verify : ∀ source table characters → Maybe (Checked source table characters)
verify source table characters = dispatch source table characters (Codec.decode table characters) refl

-- A status-only transport theorem avoids rewriting concrete native proof
-- values. Both sides still run metadata, complete payload and native checks.
data-status : I.Input → Codec.Envelope → Bool
data-status source recipes with I.check source
... | no rejected = false
... | yes metadata with Payloads.Replay.check source metadata
... | no rejected = false
... | yes payloads = present (World.G.certificate source metadata payloads
  (Codec.Envelope.families recipes) (Codec.Envelope.packets recipes))
check-data-status : ∀ source table characters recipes decoded
  → present (check-data source table characters recipes decoded) ≡ data-status source recipes
check-data-status source table characters recipes decoded with I.check source
... | no rejected = refl
... | yes metadata with Payloads.Replay.check source metadata
... | no rejected = refl
... | yes payloads = Finish.finish-status source metadata payloads table characters recipes decoded

dispatch-status : ∀ source table characters result decoded recipes → result ≡ just recipes
  → present (dispatch source table characters result decoded) ≡ data-status source recipes
dispatch-status source table characters nothing decoded recipes ()
dispatch-status source table characters (just restored) decoded .restored refl =
  check-data-status source table characters restored decoded
verify-decoded : ∀ source table characters recipes → Codec.decode table characters ≡ just recipes
  → present (verify source table characters) ≡ data-status source recipes
verify-decoded source table characters recipes found =
  dispatch-status source table characters (Codec.decode table characters) refl recipes found

verify-encoding : ∀ source table recipes node → Codec.to-node table recipes ≡ just node
  → present (verify source table (Wire.encode node)) ≡ data-status source recipes
verify-encoding source table recipes node encoded =
  verify-decoded source table (Wire.encode node) recipes (Codec.character-fidelity table recipes node encoded)
