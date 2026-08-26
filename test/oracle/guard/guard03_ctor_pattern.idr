%default total

-- Faithful transliteration of guard03_ctor_pattern.cure. Idris has no
-- Haskell-style pattern guards, so a Cure `S(k) when isZ(k)` arm that falls
-- through to a following same-constructor arm collapses into an `if` inside
-- that constructor's `case` branch — the exact semantics Cure must produce.
data N = Z | S N

isZ : N -> Bool
isZ Z = True
isZ (S _) = False

classify : N -> N
classify n = case n of
  S k => if isZ k then Z else S Z
  Z => S (S Z)

start : N
start = classify (S Z)
