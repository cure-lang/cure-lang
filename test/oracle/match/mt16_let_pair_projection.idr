%default total

data N = Z | S N

g : N
g = let p : (N, N) = (Z, S Z) in snd p
