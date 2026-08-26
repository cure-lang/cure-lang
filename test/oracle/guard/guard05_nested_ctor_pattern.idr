%default total

-- Faithful transliteration of guard05_nested_ctor_pattern.cure. Idris has no
-- pattern guards, so the guarded nested arm `S(S k) when isZ k` collapses into
-- an `if` inside that nested case branch, with the following same-shaped arm as
-- the `else` (the fall-through). accept/accept.
data N = Z | S N

isZ : N -> Bool
isZ Z = True
isZ (S _) = False

classify : N -> N
classify n = case n of
  S (S k) => if isZ k then Z else S Z
  S Z     => S (S Z)
  Z       => S (S (S Z))

start : N
start = classify (S (S Z))
