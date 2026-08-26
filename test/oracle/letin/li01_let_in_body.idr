%default total
data N = Z | S N
add : N -> N -> N
add Z b = b
add (S k) b = S (add k b)
f : N -> N
f n = let m = S n in add m m
start : N
start = f Z
