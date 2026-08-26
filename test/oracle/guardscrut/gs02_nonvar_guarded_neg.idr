%default total

data N = Z | S N

classify : Int -> N
classify n = case n + 1 of
  x => if x == 0 then Z else x

start : N
start = classify 0
