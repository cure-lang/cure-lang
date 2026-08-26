%default total

-- Idris2 has no anonymous unions: the throwaway heterogeneity that Cure expresses
-- as `Int | Bool | Atom` must be given a NAMED sum, declared up front, that exists
-- only to be a container tag. That is precisely the boilerplate the Cure feature
-- removes -- the constructs are equi-expressive, the Cure one is anonymous.
data Val = VInt Int | VBool Bool | VAtom String

describe : Val -> Int
describe (VInt n)  = n
describe (VBool _) = 1
describe (VAtom _) = 2

useInt : Int
useInt = describe (VInt 7)
