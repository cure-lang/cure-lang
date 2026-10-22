------------------------------------------------------------------------
-- A SERIALISED WIRE FORMAT for replayed certificate data, with a CHECKED
-- codec. Nothing here trusts the bytes.
--
-- STRUCTURE. A tree is first flattened to a PREFIX-FREE INSTRUCTION
-- stream (`instructions`), and the stream is decoded by a STACK MACHINE
-- (`run`) whose recursion is structural on the stream — no fuel, no
-- well-foundedness side conditions. The instruction stream is then
-- RENDERED to characters (`render`) and the rendering is proved INJECTIVE,
-- so the character string determines the stream, and hence the tree,
-- uniquely.
--
--   instruction  characters            meaning
--   i-atom n     '1'…'1' ';'           leaf holding the natural n
--   i-open       '('                   open a child list
--   i-close      ')'                   close the current child list
--
-- Natural payloads are unary so the round-trip needs no arithmetic
-- lemmas; a compact decimal or JSON layer would need its own checked
-- representation refinement, rather than being assumed faithful.
--
-- NAMES ARE INTERNED. A character-faithful round-trip for `String` is NOT
-- available here: the standard library only offers injectivity of
-- `primStringToList`/`primStringFromList`, and the missing round-trip
-- (`fromList∘toList`) exists only as a postulate in `Data.String.Unsafe`,
-- which this development does not use. The wire therefore carries a name
-- TABLE INDEX, exactly as the canonical snapshot resolves owner-qualified
-- keys against its registry: encoding is partial (a name absent from the
-- table cannot be written) and decoding looks the index up.
--
-- BOUNDARY. The structural scanner and stack machine decode characters
-- end to end. Reflected terms additionally require canonical code shape:
-- the internal defaulting retraction is NOT trusted as an input parser.
-- Names still require the caller-supplied table; source/producer fidelity
-- and the recipe payload layers are separate obligations.
------------------------------------------------------------------------
module Core.Wire where

open import Data.Char using (Char; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Data.List.Properties using (length-++)
open import Data.Nat using (pred)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ; reverse-involutive; unfold-reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Core.Syntax using (Name; Term)
open import Core.Signature using (just-inj; nothing≠just)
import Data.String.Properties as String
import Core.SyntaxEquality as Syntax

------------------------------------------------------------------------
-- Alphabet
------------------------------------------------------------------------

one : Char
one = '1'

stop : Char
stop = ';'

open-paren close-paren : Char
open-paren = '('
close-paren = ')'

one≠stop : one ≢ stop
one≠stop = λ ()

one≠open : one ≢ open-paren
one≠open = λ ()

one≠close : one ≢ close-paren
one≠close = λ ()

stop≠open : stop ≢ open-paren
stop≠open = λ ()

stop≠close : stop ≢ close-paren
stop≠close = λ ()

open≠close : open-paren ≢ close-paren
open≠close = λ ()

------------------------------------------------------------------------
-- Trees and their instruction streams
------------------------------------------------------------------------

data Node : Set where
  n-atom : ℕ → Node
  n-list : List Node → Node

data Instr : Set where
  i-atom : ℕ → Instr
  i-open : Instr
  i-close : Instr

instructions : Node → List Instr
instructions-items : List Node → List Instr
instructions (n-atom k) = i-atom k ∷ []
instructions (n-list nodes) = i-open ∷ instructions-items nodes ++ (i-close ∷ [])
instructions-items [] = []
instructions-items (node ∷ nodes) = instructions node ++ instructions-items nodes

------------------------------------------------------------------------
-- The decoding machine
--
-- The stack holds one CHILD ACCUMULATOR per open list, most recent first.
-- Children are accumulated in WRITE order and a list closes when its
-- `i-close` arrives, so no reversal is needed.
------------------------------------------------------------------------

machine : List (List Node) → List Instr → Maybe Node
machine-after : Node → List (List Node) → List Instr → Maybe Node

machine [] [] = nothing
machine [] (i-atom k ∷ is) = machine-after (n-atom k) [] is
machine [] (i-open ∷ is) = machine ([] ∷ []) is
machine [] (i-close ∷ is) = nothing
machine (acc ∷ frames) (i-atom k ∷ is) = machine-after (n-atom k) (acc ∷ frames) is
machine (acc ∷ frames) (i-open ∷ is) = machine ([] ∷ acc ∷ frames) is
machine (acc ∷ frames) (i-close ∷ is) = machine-after (n-list acc) frames is
machine (acc ∷ frames) [] = nothing

machine-after node [] [] = just node
machine-after node [] (i ∷ is) = nothing
machine-after node (acc ∷ frames) is = machine ((acc ++ (node ∷ [])) ∷ frames) is

run : List Instr → Maybe Node
run = machine []

-- Reading the children of one list: the accumulator grows by exactly the
-- child list, and the list is closed and delivered to the parent.
items-lemma : ∀ nodes acc frames is
  → machine (acc ∷ frames) (instructions-items nodes ++ (i-close ∷ is))
  ≡ machine-after (n-list (acc ++ nodes)) frames is
-- Reading one node into the innermost open list.
node-lemma : ∀ node acc frames is
  → machine (acc ∷ frames) (instructions node ++ is)
  ≡ machine-after node (acc ∷ frames) is

run-instructions : ∀ node → run (instructions node) ≡ just node
run-instructions (n-atom k) = refl
run-instructions (n-list nodes) = items-lemma nodes [] [] []

items-lemma [] acc frames is =
  cong (λ acc′ → machine-after (n-list acc′) frames is) (sym (++-identityʳ acc))
items-lemma (node ∷ nodes) acc frames is =
  trans (cong (λ rest → machine (acc ∷ frames) rest)
      (++-assoc (instructions node) (instructions-items nodes) (i-close ∷ is)))
    (trans (node-lemma node acc frames (instructions-items nodes ++ (i-close ∷ is)))
    (trans (items-lemma nodes (acc ++ (node ∷ [])) frames is)
      (cong (λ acc′ → machine-after (n-list acc′) frames is)
        (++-assoc acc (node ∷ []) nodes))))

node-lemma (n-atom k) acc frames is = refl
node-lemma (n-list nodes) acc frames is =
  trans (cong (λ rest → machine ([] ∷ acc ∷ frames) rest)
      (++-assoc (instructions-items nodes) (i-close ∷ []) is))
    (trans (items-lemma nodes [] (acc ∷ frames) is)
      (cong (λ ns → machine-after (n-list ns) (acc ∷ frames) is)
        (++-identityˡ nodes)))

------------------------------------------------------------------------
-- Rendering to characters, proved UNAMBIGUOUS
------------------------------------------------------------------------

unary : ℕ → List Char
unary zero = []
unary (suc n) = one ∷ unary n

render : Instr → List Char
render (i-atom k) = unary k ++ (stop ∷ [])
render i-open = open-paren ∷ []
render i-close = close-paren ∷ []

render-items : List Instr → List Char
render-items [] = []
render-items (i ∷ is) = render i ++ render-items is

unary-length : ∀ n → length (unary n) ≡ n
unary-length zero = refl
unary-length (suc n) = cong suc (unary-length n)

unary-rendering-length : ∀ n → length (unary n ++ stop ∷ []) ≡ suc n
unary-rendering-length n =
  trans (length-++ (unary n))
    (trans (cong (λ m → m + length (stop ∷ [])) (unary-length n))
      (trans (+-suc n zero) (cong suc (+-identityʳ n))))

-- Unary runs are prefix-free on their own: equal renderings imply equal
-- lengths (the terminator makes the two runs the same length).
unary-injective : ∀ m n → unary m ++ stop ∷ [] ≡ unary n ++ stop ∷ [] → m ≡ n
unary-injective m n eq =
  cong pred (trans (sym (unary-rendering-length m))
    (trans (cong length eq) (unary-rendering-length n)))

-- The first character of an instruction's rendering, and the rest.
first : Instr → Char
first (i-atom zero) = stop
first (i-atom (suc k)) = one
first i-open = open-paren
first i-close = close-paren

FirstOf : Instr → Set
FirstOf i = Σ (List Char) (λ rest → render i ≡ first i ∷ rest)

head-of : ∀ i → FirstOf i
head-of (i-atom zero) = [] , refl
head-of (i-atom (suc k)) = unary k ++ (stop ∷ []) , refl
head-of i-open = [] , refl
head-of i-close = [] , refl

head-eq : ∀ {x y : Char} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
head-eq refl = refl

first-eq : ∀ i j → render i ≡ render j → first i ≡ first j
first-eq i j eq =
  head-eq (trans (sym (proj₂ (head-of i))) (trans eq (proj₂ (head-of j))))

-- A single instruction's rendering determines the instruction, so the
-- characters carry the instruction stream without ambiguity.
render-injective : ∀ i j → render i ≡ render j → i ≡ j
render-injective (i-atom m) (i-atom n) eq = cong i-atom (unary-injective m n eq)
render-injective (i-atom zero) i-open eq =
  ⊥-elim (stop≠open (first-eq (i-atom zero) i-open eq))
render-injective (i-atom zero) i-close eq =
  ⊥-elim (stop≠close (first-eq (i-atom zero) i-close eq))
render-injective (i-atom (suc m)) i-open eq =
  ⊥-elim (one≠open (first-eq (i-atom (suc m)) i-open eq))
render-injective (i-atom (suc m)) i-close eq =
  ⊥-elim (one≠close (first-eq (i-atom (suc m)) i-close eq))
render-injective i-open (i-atom zero) eq =
  ⊥-elim (stop≠open (sym (first-eq i-open (i-atom zero) eq)))
render-injective i-open (i-atom (suc n)) eq =
  ⊥-elim (one≠open (sym (first-eq i-open (i-atom (suc n)) eq)))
render-injective i-open i-close eq = ⊥-elim (open≠close (first-eq i-open i-close eq))
render-injective i-close (i-atom zero) eq =
  ⊥-elim (stop≠close (sym (first-eq i-close (i-atom zero) eq)))
render-injective i-close (i-atom (suc n)) eq =
  ⊥-elim (one≠close (sym (first-eq i-close (i-atom (suc n)) eq)))
render-injective i-close i-open eq =
  ⊥-elim (open≠close (sym (first-eq i-close i-open eq)))
render-injective i-open i-open eq = refl
render-injective i-close i-close eq = refl

------------------------------------------------------------------------
-- Name interning
------------------------------------------------------------------------

index-of : (name : Name) (table : List Name) → Maybe ℕ
index-of name [] = nothing
index-of name (x ∷ table) with name String.≟ x
... | yes same = just zero
... | no different with index-of name table
...   | nothing = nothing
...   | just i = just (suc i)

lookup-at : ℕ → List Name → Maybe Name
lookup-at zero [] = nothing
lookup-at zero (x ∷ table) = just x
lookup-at (suc i) [] = nothing
lookup-at (suc i) (x ∷ table) = lookup-at i table

-- An index produced by `index-of` really points at that name, so an
-- interned wire payload decodes to the name that was written.

index-of-sound : ∀ name table i
  → index-of name table ≡ just i → lookup-at i table ≡ just name
index-of-sound name [] i ()
index-of-sound name (x ∷ table) i found with name String.≟ x
... | yes refl =
  subst (λ index → lookup-at index (x ∷ table) ≡ just name)
    (just-inj found) refl
... | no different with index-of name table in nested
...   | nothing = ⊥-elim (nothing≠just found)
...   | just j = subst (λ index → lookup-at index (x ∷ table) ≡ just name)
      (just-inj found) (index-of-sound name table j nested)

------------------------------------------------------------------------
-- THE CHARACTER-LEVEL SCANNER
--
-- Scanning is a FOLD over the character list: one character per step,
-- structural recursion, no fuel and no termination side condition. The
-- state records whether a unary run is open, and instructions are
-- accumulated in reverse.
--
-- `scan-encode` proves that scanning the rendering of ANY instruction
-- stream returns that stream, so `decode` (scan then run) inverts `encode`
-- (instructions then render) for every tree.
------------------------------------------------------------------------

data Mode : Set where
  m-ready : Mode
  m-digits : ℕ → Mode

record ScanState : Set where
  constructor scan-st
  field
    scan-mode : Mode
    scan-done : List Instr

step-ready-close : ScanState → Char → Maybe ScanState
step-ready-close s c with c ≟ close-paren
... | yes refl = just (scan-st m-ready (i-close ∷ ScanState.scan-done s))
... | no other = nothing

step-ready-open : ScanState → Char → Maybe ScanState
step-ready-open s c with c ≟ open-paren
... | yes refl = just (scan-st m-ready (i-open ∷ ScanState.scan-done s))
... | no other = step-ready-close s c

step-ready-symbol : ScanState → Char → Maybe ScanState
step-ready-symbol s c with c ≟ stop
... | yes refl = just (scan-st m-ready (i-atom 0 ∷ ScanState.scan-done s))
... | no other = step-ready-open s c

step-ready : ScanState → Char → Maybe ScanState
step-ready s c with c ≟ one
... | yes refl = just (scan-st (m-digits 1) (ScanState.scan-done s))
... | no other = step-ready-symbol s c

step-digits-stop : ScanState → ℕ → Char → Maybe ScanState
step-digits-stop s k c with c ≟ stop
... | yes refl = just (scan-st m-ready (i-atom k ∷ ScanState.scan-done s))
... | no other = nothing

step-digits : ScanState → ℕ → Char → Maybe ScanState
step-digits s k c with c ≟ one
... | yes refl = just (scan-st (m-digits (suc k)) (ScanState.scan-done s))
... | no other = step-digits-stop s k c

step : ScanState → Char → Maybe ScanState
step s c with ScanState.scan-mode s
... | m-ready = step-ready s c
... | m-digits k = step-digits s k c

apply : ScanState → List Char → Maybe ScanState
apply s [] = just s
apply s (c ∷ cs) with step s c
... | nothing = nothing
... | just next = apply next cs

finish : ScanState → Maybe (List Instr)
finish s with ScanState.scan-mode s
... | m-ready = just (reverse (ScanState.scan-done s))
... | m-digits k = nothing

maybe-finish : Maybe ScanState → Maybe (List Instr)
maybe-finish nothing = nothing
maybe-finish (just s) = finish s

scan : List Char → Maybe (List Instr)
scan cs = maybe-finish (apply (scan-st m-ready []) cs)

------------------------------------------------------------------------
-- The scanner round-trips the rendering
------------------------------------------------------------------------

one-plus : ∀ k → suc zero + k ≡ suc k
one-plus zero = refl
one-plus (suc k) = cong suc (one-plus k)

suc-shuffle : ∀ j k → suc j + k ≡ j + suc k
suc-shuffle j k = sym (+-suc j k)

-- A unary run scanned from an open run of length `j`.
apply-digits : ∀ d j k
  → apply (scan-st (m-digits j) d) (unary k ++ stop ∷ [])
  ≡ just (scan-st m-ready (i-atom (j + k) ∷ d))
apply-digits d j zero =
  cong (λ n → just (scan-st m-ready (i-atom n ∷ d))) (sym (+-identityʳ j))
apply-digits d j (suc k) =
  trans (apply-digits d (suc j) k)
    (cong (λ n → just (scan-st m-ready (i-atom n ∷ d))) (suc-shuffle j k))

-- A unary atom scanned from the ready state.
apply-atom : ∀ d k
  → apply (scan-st m-ready d) (unary k ++ stop ∷ [])
  ≡ just (scan-st m-ready (i-atom k ∷ d))
apply-atom d zero = refl
apply-atom d (suc k) =
  trans (apply-digits d 1 k)
    (cong (λ n → just (scan-st m-ready (i-atom n ∷ d))) (one-plus k))

apply-instr : ∀ i d
  → apply (scan-st m-ready d) (render i)
  ≡ just (scan-st m-ready (i ∷ d))
apply-instr (i-atom k) d = apply-atom d k
apply-instr i-open d = refl
apply-instr i-close d = refl

maybe-apply : Maybe ScanState → List Char → Maybe ScanState
maybe-apply nothing cs = nothing
maybe-apply (just s) cs = apply s cs

apply-append : ∀ s xs ys → apply s (xs ++ ys) ≡ maybe-apply (apply s xs) ys
apply-append s [] ys = refl
apply-append s (x ∷ xs) ys with step s x
... | nothing = refl
... | just next = apply-append next xs ys

apply-stream : ∀ is d
  → apply (scan-st m-ready d) (render-items is)
  ≡ just (scan-st m-ready (reverse is ++ d))
apply-stream [] d = refl
apply-stream (i ∷ is) d =
  trans (apply-append (scan-st m-ready d) (render i) (render-items is))
    (trans (cong (λ next → maybe-apply next (render-items is)) (apply-instr i d))
      (trans (apply-stream is (i ∷ d))
        (cong (λ dst → just (scan-st m-ready dst))
          (sym (trans (cong (λ xs → xs ++ d) (unfold-reverse i is))
            (++-assoc (reverse is) (i ∷ []) d))))))

scan-encode : ∀ is → scan (render-items is) ≡ just is
scan-encode is =
  trans (cong maybe-finish (apply-stream is []))
    (trans (cong (λ d → just (reverse d)) (++-identityʳ (reverse is)))
      (cong (λ xs → just xs) (reverse-involutive is)))

------------------------------------------------------------------------
-- End-to-end: the characters encode the tree
------------------------------------------------------------------------

encode : Node → List Char
encode = render-items ∘ instructions

maybe-run : Maybe (List Instr) → Maybe Node
maybe-run nothing = nothing
maybe-run (just is) = run is

decode : List Char → Maybe Node
decode cs = maybe-run (scan cs)

decode-encode : ∀ node → decode (encode node) ≡ just node
decode-encode node with scan (render-items (instructions node)) | scan-encode (instructions node)
... | .(just (instructions node)) | refl = run-instructions node

------------------------------------------------------------------------
-- REFLECTED CODES ON THE WIRE
--
-- Terms travel as `Core.SyntaxEquality.Code`, whose `encode`/`decode` pair
-- is ALREADY proved to be a retraction (`Syntax.roundtrip`). This layer
-- therefore only has to carry codes faithfully: the tag and the two
-- naturals directly, the children recursively, and the NAME as a table
-- index (proved sound above). Term fidelity then follows from that
-- existing theorem — no new term-level argument is assumed.
------------------------------------------------------------------------

mutual
  code-to-node : (table : List Name) → Syntax.Code → Maybe Node
  code-to-node table (Syntax.node tag name number kids) with index-of name table
  ... | nothing = nothing
  ... | just i = code-kids table tag i number kids

  code-kids : (table : List Name) → ℕ → ℕ → ℕ → List Syntax.Code → Maybe Node
  code-kids table tag i number kids with encode-kids table kids
  ... | nothing = nothing
  ... | just nodes = just (n-list (n-atom tag ∷ n-atom i ∷ n-atom number ∷ nodes))

  encode-kids : (table : List Name) → List Syntax.Code → Maybe (List Node)
  encode-kids table [] = just []
  encode-kids table (code ∷ codes) with code-to-node table code
  ... | nothing = nothing
  ... | just node with encode-kids table codes
  ...   | nothing = nothing
  ...   | just nodes = just (node ∷ nodes)

mutual
  wire-to-code : (table : List Name) → Node → Maybe Syntax.Code
  wire-to-code table (n-atom k) = nothing
  wire-to-code table (n-list (n-atom tag ∷ n-atom i ∷ n-atom number ∷ nodes))
    with lookup-at i table
  ... | nothing = nothing
  ... | just name = wire-code table name tag number nodes
  wire-to-code table (n-list other) = nothing

  wire-code : (table : List Name) → Name → ℕ → ℕ → List Node → Maybe Syntax.Code
  wire-code table name tag number nodes with decode-kids table nodes
  ... | nothing = nothing
  ... | just codes = just (Syntax.node tag name number codes)

  maybe-prepend : Syntax.Code → Maybe (List Syntax.Code) → Maybe (List Syntax.Code)
  maybe-prepend code nothing = nothing
  maybe-prepend code (just codes) = just (code ∷ codes)

  maybe-decode : (table : List Name) → Maybe Syntax.Code → List Node
    → Maybe (List Syntax.Code)
  maybe-decode table nothing nodes = nothing
  maybe-decode table (just code) nodes = maybe-prepend code (decode-kids table nodes)

  decode-kids : (table : List Name) → List Node → Maybe (List Syntax.Code)
  decode-kids table [] = just []
  decode-kids table (node ∷ nodes) =
    maybe-decode table (wire-to-code table node) nodes

------------------------------------------------------------------------
-- Code fidelity
------------------------------------------------------------------------

mutual
  code-fidelity : ∀ table code node
    → code-to-node table code ≡ just node → wire-to-code table node ≡ just code
  code-fidelity table (Syntax.node tag name number kids) node found
    with index-of name table in indexed
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just i with encode-kids table kids in encoded
  ...   | nothing = ⊥-elim (nothing≠just found)
  ...   | just nodes =
        subst (λ target → wire-to-code table target
            ≡ just (Syntax.node tag name number kids))
          (just-inj found)
          (wire-code-at table name tag i number kids nodes indexed encoded)

  wire-code-at : ∀ table name tag i number kids nodes
    → index-of name table ≡ just i
    → encode-kids table kids ≡ just nodes
    → wire-to-code table (n-list (n-atom tag ∷ n-atom i ∷ n-atom number ∷ nodes))
      ≡ just (Syntax.node tag name number kids)
  wire-code-at table name tag i number kids nodes indexed encoded
    rewrite index-of-sound name table i indexed
          | kids-fidelity table kids nodes encoded = refl

  kids-fidelity : ∀ table codes nodes
    → encode-kids table codes ≡ just nodes → decode-kids table nodes ≡ just codes
  kids-fidelity table [] nodes found with just-inj found
  ... | refl = refl
  kids-fidelity table (code ∷ codes) nodes found
    with code-to-node table code in converted
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just node with encode-kids table codes in encoded
  ...   | nothing = ⊥-elim (nothing≠just found)
  ...   | just nodes′ =
        subst (λ target → decode-kids table target ≡ just (code ∷ codes))
          (just-inj found)
          (trans (cong (λ next → maybe-decode table next nodes′)
                   (code-fidelity table code node converted))
            (trans (cong (maybe-prepend code)
                     (kids-fidelity table codes nodes′ encoded))
              refl))

------------------------------------------------------------------------
-- Term fidelity, through the existing proved retraction
------------------------------------------------------------------------

term-to-wire : (table : List Name) → Term → Maybe Node
term-to-wire table term = code-to-node table (Syntax.encode term)
checked-term : Syntax.Code → Maybe Term
checked-term code with Syntax.code-equal? (Syntax.encode (Syntax.decode code)) code
... | yes canonical = just (Syntax.decode code)
... | no malformed = nothing

checked-term-at : ∀ code term → Syntax.decode code ≡ term → Syntax.encode term ≡ code
  → checked-term code ≡ just term
checked-term-at code term decoded encoded
  with Syntax.code-equal? (Syntax.encode (Syntax.decode code)) code
... | yes canonical = cong just decoded
... | no unequal = ⊥-elim (unequal (trans (cong Syntax.encode decoded) encoded))

checked-term-roundtrip : ∀ term → checked-term (Syntax.encode term) ≡ just term
checked-term-roundtrip term =
  checked-term-at (Syntax.encode term) term (Syntax.roundtrip term) refl

-- Successful validation preserves EVERY code field and child. In
-- particular, unknown tags, defaulted levels/grades and wrong child
-- shapes cannot silently become a different valid Term.
checked-term-exact : ∀ code term → checked-term code ≡ just term → Syntax.encode term ≡ code
checked-term-exact code term found
  with Syntax.code-equal? (Syntax.encode (Syntax.decode code)) code
... | no malformed = ⊥-elim (nothing≠just found)
... | yes canonical with just-inj found
... | refl = canonical

wire-to-term : (table : List Name) → Node → Maybe Term
wire-to-term table node with wire-to-code table node
... | nothing = nothing
... | just code = checked-term code

wire-to-term-exact : ∀ table node term → wire-to-term table node ≡ just term
  → Σ Syntax.Code (λ code → wire-to-code table node ≡ just code × Syntax.encode term ≡ code)
wire-to-term-exact table node term found with wire-to-code table node
... | nothing = ⊥-elim (nothing≠just found)
... | just code = code , refl , checked-term-exact code term found

term-fidelity : ∀ table term node
  → term-to-wire table term ≡ just node → wire-to-term table node ≡ just term
term-fidelity table term node found
  rewrite code-fidelity table (Syntax.encode term) node found =
  checked-term-roundtrip term

------------------------------------------------------------------------
-- End-to-end term pipeline: characters ↔ reflected code ↔ term
------------------------------------------------------------------------

maybe-term : (table : List Name) → Maybe Node → Maybe Term
maybe-term table nothing = nothing
maybe-term table (just node) = wire-to-term table node

decode-term : (List Name) → List Char → Maybe Term
decode-term table cs = maybe-term table (decode cs)

decode-term-fidelity : ∀ table term node
  → term-to-wire table term ≡ just node
  → decode-term table (encode node) ≡ just term
decode-term-fidelity table term node found
  rewrite decode-encode node
        | term-fidelity table term node found = refl
