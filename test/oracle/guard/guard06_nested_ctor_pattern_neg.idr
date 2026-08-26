%default total

-- Adversarial control for guard05_nested_ctor_pattern: the guarded nested
-- branch body has the wrong type (Other, not N), so the folded `if` fails to
-- type-check. reject/reject.
data N = Z | S N
data Other = A | B

isZ : N -> Bool
isZ Z = True
isZ (S _) = False

classify : N -> N
classify n = case n of
  S (S k) => if isZ k then A else S Z
  S Z     => S (S Z)
  Z       => S (S (S Z))

start : N
start = classify (S (S Z))
