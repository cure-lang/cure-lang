%default total
data N = Z | S N
add : N -> N -> N
add Z b = b
add (S k) b = S (add k b)
f : N -> N
f p = add (let d = S p in add d d) p
start : N
start = f (S Z)
