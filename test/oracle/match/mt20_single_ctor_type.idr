%default total

data N = Z | S N

data Box = MkBox N

un : Box -> N
un b = case b of
         MkBox x => x

g : N
g = un (MkBox (S Z))
