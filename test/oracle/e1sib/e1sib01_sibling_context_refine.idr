%default total

-- E1 mirror (the headline): a dependent match on the EVIDENCE refines the whole
-- local context, not just the motive. Matching `SendSendK` forces the sibling
-- `b` to `BSend y k`, so the clause need only cover the `BSend` shape — the `BNil`
-- and `BRecv` shapes are impossible under the refinement. Idris does this by
-- refining the context on the dependent match; Cure now does too (the sibling
-- binder `b` is specialised by the branch-unify substitution). Idris folds the two
-- scrutinees into one clause head; Cure spells the nested `match b`. Same proof,
-- each language's idiom. `t` is implicit here (fixed by the `SendsIn` index).

data Tag = TA | TB
data Behaviour = BNil | BRecv Tag Behaviour | BSend Tag Behaviour
data TagList = TNil | TCons Tag TagList

infer : Behaviour -> TagList
infer BNil        = TNil
infer (BRecv t k) = infer k
infer (BSend t k) = TCons t (infer k)

data Member : Tag -> TagList -> Type where
  MemHere  : Member t (TCons t rest)
  MemThere : Member t rest -> Member t (TCons y rest)

data SendsIn : Behaviour -> Tag -> Type where
  SendHere  : SendsIn (BSend t k) t
  SendSendK : SendsIn k t -> SendsIn (BSend y k) t

coverage : (b : Behaviour) -> SendsIn b t -> Member t (infer b)
coverage (BSend t k) SendHere       = MemHere
coverage (BSend y k) (SendSendK s2) = MemThere (coverage k s2)
