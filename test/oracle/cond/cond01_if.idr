%default total

data N = Z | S N

f : Bool -> N
f b = if b then S Z else Z

start : N
start = f True
