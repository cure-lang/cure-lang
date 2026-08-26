%default total

data N = Z | S N
data B = T | F

foo : N -> N
foo n =
  let b = case n of { Z => Z; S k => T } in
  case b of
    Z => Z
    S k => Z
