%default total

-- A parameter whose type is a DEPENDENT function `(n : N) -> P n`: the codomain
-- mentions the domain binder `n`. `f m` then has type `P m`. Explicit dependent
-- arrow with a concrete codomain family — isolates the dependent-arrow surface
-- feature from higher-order implicit inference (no metavariable to solve).
-- Faithful transliteration of dep08_dependent_arrow_param.cure — accept/accept.

data N = Z | S N

data P : N -> Type where
  Mkp : P n

ap2 : ((n : N) -> P n) -> (m : N) -> P m
ap2 f m = f m
