%default total

data Color = Red | Green | Blue
data N = Z | S N

tag : Color -> N
tag c = case c of
          Red => Z
          other => S Z
