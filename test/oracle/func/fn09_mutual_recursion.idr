%default total

data N = Zero | Suc N

mutual
  ping : N -> N
  ping Zero = Zero
  ping (Suc k) = Suc (pong k)

  pong : N -> N
  pong Zero = Zero
  pong (Suc k) = Suc (ping k)

g : N
g = ping (Suc (Suc Zero))
