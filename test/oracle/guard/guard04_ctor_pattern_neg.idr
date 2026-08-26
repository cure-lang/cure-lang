%default total

-- Adversarial control for guard03_ctor_pattern: the guarded branch body has the
-- wrong type (Other, not N), so the folded `if` inside the `S` case branch fails
-- to type-check. Faithful transliteration — reject/reject.
data N = Z | S N
data Other = A | B

isZ : N -> Bool
isZ Z = True
isZ (S _) = False

classify : N -> N
classify n = case n of
  S k => if isZ k then A else S Z
  Z => S (S Z)

start : N
start = classify (S Z)
