%default total

data N = Z | S N

data Opt a = None | Some a

empty : Opt N
empty = None

g : N
g = case empty of
      Some x => x
      None => Z
