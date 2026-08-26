%default total

data N = Z | S N
data P = MkP N N | Nil

h : P -> N
h p = case p of
        MkP Z Z => Z
        MkP Z (S b) => b
        MkP (S a) y => a
        Nil => Z
