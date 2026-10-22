{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- Native checking of the bounded semantic-context MODEL. No arbitrary
-- semantic readback/evaluation assumption or context-typing callback.
------------------------------------------------------------------------
module Core.FlatContextTyping where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
import Data.Fin as Fin
import Data.Vec as V
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax
open import Core.Grade using (Grade)
open import Core.Universe using (Level)
open import Core.Typing using (Ctx; ⟨⟩; extend; lookup)
open import Core.NativeRecipe using (r-leaf)
import Core.FlatContext as F
import Core.CheckedAdmission as Admission
import Core.LocalFrame as Substitution
import Proof.DependentCoherence as Coherence
import Proof.DependentGeneralTransport as General

data Operation : Set where
  bind-opaque : F.Value → Grade → Operation
  bind-defined : F.Value → F.Value → Operation

collect : ∀ {n} (P : Fin.Fin n → Set) → ((i : Fin.Fin n) → Maybe (P i))
  → Maybe ((i : Fin.Fin n) → P i)
collect {zero} P checked = just (λ ())
collect {suc n} P checked with checked Fin.zero
... | nothing = nothing
... | just head with collect (λ i → P (Fin.suc i)) (λ i → checked (Fin.suc i))
... | nothing = nothing
... | just tail = just (λ { Fin.zero → head ; (Fin.suc i) → tail i })

module Replay {source table certificate-chars}
  (source-checked : Admission.Checked source table certificate-chars) where
  module C = Admission.Checked source-checked
  module N = C.W.N
  module D = C.W.G.D
  module Frames = Coherence.NativeFrames C.W.ind C.W.sig C.W.M.conversion
  module Transport = General.General C.W.ind C.W.sig C.W.M.conversion
  module T = Transport.Valid C.valid

  data Typed : ∀ {n} {ctx : F.Store source n} {Γ : Ctx n} → F.Built ctx Γ → Set where
    t-empty : Typed F.b-empty
    t-opaque : ∀ {n} {ctx : F.Store source n} {Γ ty term grade level}
      {built : F.Built ctx Γ} {read : F.Reads n ty term}
      → Typed built → N._⊢_⇒_ Γ term (tm-type level) → Typed (F.b-opaque built read grade)
    t-defined : ∀ {n} {ctx : F.Store source n} {Γ ty term value quoted level}
      {built : F.Built ctx Γ} {read : F.Reads n ty term} {value-read : F.Reads n value quoted}
      → Typed built → N._⊢_⇒_ Γ term (tm-type level) → N._⊢_⇒_ Γ quoted term
      → Typed (F.b-defined built read value-read)
  typed-wf : ∀ {n} {ctx : F.Store source n} {Γ : Ctx n} {built : F.Built ctx Γ}
    → Typed built → N.WellFormed Γ
  typed-wf t-empty = N.wf[]
  typed-wf (t-opaque {read = read} before kind) = N.wf∷ (typed-wf before) (F.scoped read) kind
  typed-wf (t-defined {read = read} before kind value) = N.wf∷ (typed-wf before) (F.scoped read) kind

  record Frame : Set where
    field
      size : ℕ
      store : F.Store source size
      context : Ctx size
      built : F.Built store context
      typing : Typed built
    well-formed : N.WellFormed context
    well-formed = typed-wf typing
    environment : V.Vec Term size
    environment = F.environment-terms built
    substitution : Sub
    substitution = Substitution.prefix (V.toList environment) Substitution.identity
    types-read : F.quote-values size (F.types store) ≡ just (F.context-types context)
    types-read = F.values-complete (F.type-view built)
    environment-read : F.quote-values size (F.environment store) ≡ just environment
    environment-read = F.values-complete (F.environment-view built)

  start : Frame
  start = record { size = 0 ; store = F.empty source ; context = ⟨⟩ ; built = F.b-empty ; typing = t-empty }
  go : Frame → List Operation → Maybe Frame
  go frame [] = just frame
  go frame (bind-opaque ty grade ∷ rest) with F.reify (Frame.size frame) ty in read
  ... | nothing = nothing
  ... | just term with D.kind (Frame.context frame) term r-leaf
  ... | nothing = nothing
  ... | just (level , kind) = go record
    { size = suc (Frame.size frame) ; store = F.extend-opaque (Frame.store frame) ty grade
    ; context = extend (Frame.context frame) term
    ; built = F.b-opaque (Frame.built frame) (F.quote-sound _ ty term read) grade
    ; typing = t-opaque (Frame.typing frame) kind } rest
  go frame (bind-defined ty value ∷ rest) with F.reify (Frame.size frame) ty in read
  ... | nothing = nothing
  ... | just term with D.kind (Frame.context frame) term r-leaf
  ... | nothing = nothing
  ... | just (level , kind) with F.reify (Frame.size frame) value in value-read
  ... | nothing = nothing
  ... | just quoted with D.at (Frame.context frame) quoted term r-leaf
  ... | nothing = nothing
  ... | just typed = go record
    { size = suc (Frame.size frame) ; store = F.defined (Frame.store frame) ty value
    ; context = extend (Frame.context frame) term
    ; built = F.b-defined (Frame.built frame) (F.quote-sound _ ty term read)
        (F.quote-sound _ value quoted value-read)
    ; typing = t-defined (Frame.typing frame) kind typed } rest
  build : List Operation → Maybe Frame
  build = go start

  images : (frame : Frame) → Maybe (Frames.Coherent (Frame.context frame) (Frame.context frame)
    (Frame.substitution frame))
  images frame = collect
    (λ i → N._⊢_⇒_ (Frame.context frame) (Frame.substitution frame (Fin.toℕ i))
      (substS (Frame.substitution frame) (lookup (Frame.context frame) i)))
    (λ i → D.at (Frame.context frame) (Frame.substitution frame (Fin.toℕ i))
      (substS (Frame.substitution frame) (lookup (Frame.context frame) i)) r-leaf)

  record Checked (operations : List Operation) : Set where
    field
      frame : Frame
      replayed : build operations ≡ just frame
      coherent : Frames.Coherent (Frame.context frame) (Frame.context frame) (Frame.substitution frame)
      images-checked : images frame ≡ just coherent
    transport : ∀ {t ty} → N._⊢_⇒_ (Frame.context frame) t ty
      → N._⊢_⇒_ (Frame.context frame) (substS (Frame.substitution frame) t)
          (substS (Frame.substitution frame) ty)
    transport = T.subst⇒ coherent (Frame.well-formed frame)

  package : ∀ operations frame → build operations ≡ just frame
    → (result : Maybe (Frames.Coherent (Frame.context frame) (Frame.context frame) (Frame.substitution frame)))
    → images frame ≡ result → Maybe (Checked operations)
  package operations frame replayed nothing checked = nothing
  package operations frame replayed (just coherent) checked = just record
    { frame = frame ; replayed = replayed ; coherent = coherent ; images-checked = checked }
  finish : ∀ operations frame → build operations ≡ just frame → Maybe (Checked operations)
  finish operations frame replayed = package operations frame replayed (images frame) refl
  dispatch : ∀ operations (result : Maybe Frame) → build operations ≡ result → Maybe (Checked operations)
  dispatch operations nothing replayed = nothing
  dispatch operations (just frame) replayed = finish operations frame replayed
  verify : (operations : List Operation) → Maybe (Checked operations)
  verify operations = dispatch operations (build operations) refl
