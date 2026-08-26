%default total

data Lst a = LNil | LCons a (Lst a)

data Rose = RNode (Lst Rose)
