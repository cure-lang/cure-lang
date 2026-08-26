%default total

data N = Z | S N

data W = MkW (N, N) | NoW

sndW : W -> N
sndW w = case w of
           MkW p => snd p
           NoW => Z

g : N
g = sndW (MkW (Z, S Z))
