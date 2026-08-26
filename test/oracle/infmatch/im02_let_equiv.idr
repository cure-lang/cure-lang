%default total

data N = Z | S N
data B = T | F

foo : N -> N
foo n =
  let b = case n of { Z => T; (S k) => F } in
  case b of
    T => Z
    F => S Z
