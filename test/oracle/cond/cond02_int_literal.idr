%default total

data N = Z | S N

classify : Int -> N
classify n = case n of
               0 => Z
               1 => S Z
               _ => S (S Z)

start : N
start = classify 1
