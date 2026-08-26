%default total

data N = Z | S N

classify : Int -> N
classify n = if n == 0 then Z else if n == 1 then S Z else S (S Z)

start : N
start = classify 1
