------------------------------------------------------------------------
-- Every ordinary Recipe constructor, including dependent r-case, on
-- the wire. Parsing returns data; native replay still checks all claims.
------------------------------------------------------------------------
module Core.WireRecipe where

open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Syntax using (Name; Term)
open import Core.Signature using (nothing≠just; just-inj)
open import Core.Universe using (Level; l0; l1; l2; toNat)
open import Core.NativeRecipe using (Recipe; r-leaf; r-pi; r-lam; r-app; r-let; r-data;
  r-ctor; r-claim; r-cumul; r-convert; r-case)
import Core.Wire as W
import Core.WireConversion as C
open W using (Node; n-atom; n-list)

collect : List (Maybe Node) → Maybe (List Node)
collect [] = just []
collect (nothing ∷ rest) = nothing
collect (just node ∷ rest) = C.map (node ∷_) (collect rest)
fields : ℕ → List (Maybe Node) → Maybe Node
fields tag values = C.map (C.tagged tag) (collect values)

level-node : Level → Node
level-node level = n-atom (toNat level)
node-level : Node → Maybe Level
node-level (n-atom 0) = just l0
node-level (n-atom 1) = just l1
node-level (n-atom 2) = just l2
node-level other = nothing
level-fidelity : ∀ level → node-level (level-node level) ≡ just level
level-fidelity l0 = refl
level-fidelity l1 = refl
level-fidelity l2 = refl

to-terms : List Name → List Term → Maybe (List Node)
to-terms table [] = just []
to-terms table (t ∷ ts) = C.pair _∷_ (W.term-to-wire table t) (to-terms table ts)
from-terms : List Name → List Node → Maybe (List Term)
from-terms table [] = just []
from-terms table (n ∷ ns) = C.pair _∷_ (W.wire-to-term table n) (from-terms table ns)
terms-fidelity : ∀ table terms nodes → to-terms table terms ≡ just nodes
  → from-terms table nodes ≡ just terms
terms-fidelity table [] nodes found with just-inj found
... | refl = refl
terms-fidelity table (t ∷ ts) nodes found with W.term-to-wire table t in encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just head with to-terms table ts in tail-encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just tail with just-inj found
... | refl rewrite W.term-fidelity table t head encoded | terms-fidelity table ts tail tail-encoded = refl

mutual
  to-node : List Name → Recipe → Maybe Node
  to-node table r-leaf = just (C.tagged 0 [])
  to-node table (r-pi a b) = C.two 1 (to-node table a) (to-node table b)
  to-node table (r-lam a b) = C.two 2 (to-node table a) (to-node table b)
  to-node table (r-app a b) = C.two 3 (to-node table a) (to-node table b)
  to-node table (r-let a b c) = C.three 4 (to-node table a) (to-node table b) (to-node table c)
  to-node table (r-data ps is) = C.two 5 (C.map n-list (to-nodes table ps)) (C.map n-list (to-nodes table is))
  to-node table (r-ctor ps prs ars) =
    C.three 6 (C.map n-list (to-terms table ps)) (C.map n-list (to-nodes table prs))
      (C.map n-list (to-nodes table ars))
  to-node table (r-claim t child) = C.two 7 (W.term-to-wire table t) (to-node table child)
  to-node table (r-cumul level child) = C.two 8 (just (level-node level)) (to-node table child)
  to-node table (r-convert t conversion child) =
    C.three 9 (W.term-to-wire table t) (C.to-node table conversion) (to-node table child)
  to-node table (r-case scrut ps is level kind motive branches) = fields 10
    (to-node table scrut ∷ C.map n-list (to-nodes table ps) ∷ C.map n-list (to-nodes table is) ∷
      just (level-node level) ∷ to-node table kind ∷ to-node table motive ∷
      C.map n-list (to-branches table branches) ∷ [])

  to-nodes : List Name → List Recipe → Maybe (List Node)
  to-nodes table [] = just []
  to-nodes table (r ∷ rs) = C.pair _∷_ (to-node table r) (to-nodes table rs)
  to-branches : List Name → List (List Recipe × Recipe) → Maybe (List Node)
  to-branches table [] = just []
  to-branches table ((kinds , body) ∷ rest) =
    C.pair _∷_
      (C.pair (λ ks b → n-list (n-list ks ∷ b ∷ [])) (to-nodes table kinds) (to-node table body))
      (to-branches table rest)

mutual
  from-node : List Name → Node → Maybe Recipe
  from-node table (n-list (n-atom 0 ∷ [])) = just r-leaf
  from-node table (n-list (n-atom 1 ∷ a ∷ b ∷ [])) = C.pair r-pi (from-node table a) (from-node table b)
  from-node table (n-list (n-atom 2 ∷ a ∷ b ∷ [])) = C.pair r-lam (from-node table a) (from-node table b)
  from-node table (n-list (n-atom 3 ∷ a ∷ b ∷ [])) = C.pair r-app (from-node table a) (from-node table b)
  from-node table (n-list (n-atom 4 ∷ a ∷ b ∷ c ∷ [])) =
    C.triple r-let (from-node table a) (from-node table b) (from-node table c)
  from-node table (n-list (n-atom 5 ∷ n-list ps ∷ n-list is ∷ [])) =
    C.pair r-data (from-nodes table ps) (from-nodes table is)
  from-node table (n-list (n-atom 6 ∷ n-list ps ∷ n-list prs ∷ n-list ars ∷ [])) =
    C.triple r-ctor (from-terms table ps) (from-nodes table prs) (from-nodes table ars)
  from-node table (n-list (n-atom 7 ∷ t ∷ child ∷ [])) =
    C.pair r-claim (W.wire-to-term table t) (from-node table child)
  from-node table (n-list (n-atom 8 ∷ level ∷ child ∷ [])) =
    C.pair r-cumul (node-level level) (from-node table child)
  from-node table (n-list (n-atom 9 ∷ t ∷ conversion ∷ child ∷ [])) =
    C.triple r-convert (W.wire-to-term table t) (C.from-node table conversion) (from-node table child)
  from-node table (n-list (n-atom 10 ∷ scrut ∷ n-list ps ∷ n-list is ∷ level ∷ kind ∷ motive ∷
      n-list branches ∷ []))
    with from-node table scrut | from-nodes table ps | from-nodes table is | node-level level |
      from-node table kind | from-node table motive | from-branches table branches
  ... | just s | just p | just i | just l | just k | just m | just bs = just (r-case s p i l k m bs)
  ... | _ | _ | _ | _ | _ | _ | _ = nothing
  from-node table other = nothing

  from-nodes : List Name → List Node → Maybe (List Recipe)
  from-nodes table [] = just []
  from-nodes table (r ∷ rs) = C.pair _∷_ (from-node table r) (from-nodes table rs)
  from-branches : List Name → List Node → Maybe (List (List Recipe × Recipe))
  from-branches table [] = just []
  from-branches table (n-list (n-list kinds ∷ body ∷ []) ∷ rest) =
    C.pair _∷_ (C.pair _,_ (from-nodes table kinds) (from-node table body)) (from-branches table rest)
  from-branches table other = nothing

mutual
  fidelity : ∀ table recipe node → to-node table recipe ≡ just node
    → from-node table node ≡ just recipe
  fidelity table r-leaf node found with just-inj found
  ... | refl = refl
  fidelity table (r-pi a b) node found with to-node table a in ea
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just na with to-node table b in eb
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nb with just-inj found
  ... | refl rewrite fidelity table a na ea | fidelity table b nb eb = refl
  fidelity table (r-lam a b) node found with to-node table a in ea
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just na with to-node table b in eb
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nb with just-inj found
  ... | refl rewrite fidelity table a na ea | fidelity table b nb eb = refl
  fidelity table (r-app a b) node found with to-node table a in ea
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just na with to-node table b in eb
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nb with just-inj found
  ... | refl rewrite fidelity table a na ea | fidelity table b nb eb = refl
  fidelity table (r-let a b c) node found with to-node table a in ea
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just na with to-node table b in eb
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nb with to-node table c in ec
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nc with just-inj found
  ... | refl rewrite fidelity table a na ea | fidelity table b nb eb | fidelity table c nc ec = refl
  fidelity table (r-data ps is) node found with to-nodes table ps in ep
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just np with to-nodes table is in ei
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just ni with just-inj found
  ... | refl rewrite each-fidelity table ps np ep | each-fidelity table is ni ei = refl
  fidelity table (r-ctor ps prs ars) node found with to-terms table ps in ep
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just np with to-nodes table prs in epr
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just npr with to-nodes table ars in ear
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nar with just-inj found
  ... | refl rewrite terms-fidelity table ps np ep | each-fidelity table prs npr epr
      | each-fidelity table ars nar ear = refl
  fidelity table (r-claim t child) node found with W.term-to-wire table t in et
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nt with to-node table child in ec
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nc with just-inj found
  ... | refl rewrite W.term-fidelity table t nt et | fidelity table child nc ec = refl
  fidelity table (r-cumul level child) node found with to-node table child in ec
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nc with just-inj found
  ... | refl rewrite level-fidelity level | fidelity table child nc ec = refl
  fidelity table (r-convert t conversion child) node found with W.term-to-wire table t in et
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nt with C.to-node table conversion in ev
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nv with to-node table child in ec
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nc with just-inj found
  ... | refl rewrite W.term-fidelity table t nt et | C.fidelity table conversion nv ev
      | fidelity table child nc ec = refl
  fidelity table (r-case scrut ps is level kind motive branches) node found with to-node table scrut in es
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just ns with to-nodes table ps in ep
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just np with to-nodes table is in ei
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just ni with to-node table kind in ek
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nk with to-node table motive in em
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nm with to-branches table branches in eb
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nb with just-inj found
  ... | refl rewrite fidelity table scrut ns es | each-fidelity table ps np ep | each-fidelity table is ni ei
      | level-fidelity level | fidelity table kind nk ek | fidelity table motive nm em
      | branches-fidelity table branches nb eb = refl

  each-fidelity : ∀ table recipes nodes → to-nodes table recipes ≡ just nodes
    → from-nodes table nodes ≡ just recipes
  each-fidelity table [] nodes found with just-inj found
  ... | refl = refl
  each-fidelity table (child ∷ children) nodes found with to-node table child in ec
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nc with to-nodes table children in er
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nr with just-inj found
  ... | refl rewrite fidelity table child nc ec | each-fidelity table children nr er = refl

  branches-fidelity : ∀ table branches nodes → to-branches table branches ≡ just nodes
    → from-branches table nodes ≡ just branches
  branches-fidelity table [] nodes found with just-inj found
  ... | refl = refl
  branches-fidelity table ((kinds , body) ∷ rest) nodes found with to-nodes table kinds in ek
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nk with to-node table body in eb
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nb with to-branches table rest in er
  ... | nothing = ⊥-elim (nothing≠just found)
  ... | just nr with just-inj found
  ... | refl rewrite each-fidelity table kinds nk ek | fidelity table body nb eb
      | branches-fidelity table rest nr er = refl

encode : List Name → Recipe → Maybe (List Char)
encode table recipe = C.map W.encode (to-node table recipe)
decode : List Name → List Char → Maybe Recipe
decode table characters with W.decode characters
... | nothing = nothing
... | just node = from-node table node
character-fidelity : ∀ table recipe node → to-node table recipe ≡ just node
  → decode table (W.encode node) ≡ just recipe
character-fidelity table recipe node found
  rewrite W.decode-encode node | fidelity table recipe node found = refl
roundtrip : ∀ table recipe characters → encode table recipe ≡ just characters
  → decode table characters ≡ just recipe
roundtrip table recipe characters found with to-node table recipe in encoded
... | nothing = ⊥-elim (nothing≠just found)
... | just node with just-inj found
... | refl = character-fidelity table recipe node encoded
