%default total

data N = Z | S N

bad : (value : N) -> value = value
bad Z = Refl
bad (S previous) = bad
