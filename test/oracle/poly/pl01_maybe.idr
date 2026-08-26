%default total

data N = Z | S N

data Opt a = None | Some a

get : N -> Opt N -> N
get d o = case o of
            Some x => x
            None => d

g : N
g = get Z (Some (S Z))
