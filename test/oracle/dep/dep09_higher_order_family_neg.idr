%default total

-- Adversarial negative control for the higher-order (Miller) inference in dep07.
-- The implicit family `F` is inferred from the lambda body's type: `n : N`, so
-- `F` solves to the constant `N` and `the2 (\n => n) m : F m = N`. But the result
-- is CLAIMED to be `M`, and `N /= M`, so this MUST be rejected — `F` is solved,
-- then the mismatched return type is caught. Faithful transliteration of
-- dep09_higher_order_family_neg.cure — reject/reject.

data N = Z | S N
data M = MZ | MS M

the2 : {F : N -> Type} -> ((n : N) -> F n) -> (m : N) -> F m
the2 g m = g m

test : (m : N) -> M
test m = the2 (\n => n) m
