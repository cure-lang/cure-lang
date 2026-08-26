%default total

data N = Z | S N

classify : Int -> N
classify n = if n == 0 then Z else S Z

start : N
start = classify 0
