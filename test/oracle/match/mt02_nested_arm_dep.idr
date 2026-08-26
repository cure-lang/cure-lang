%default total

data N = Z | S N

reflId : (n : N) -> n = n
reflId Z = Refl
reflId (S k) = case k of
  Z => Refl
  S j => Refl
