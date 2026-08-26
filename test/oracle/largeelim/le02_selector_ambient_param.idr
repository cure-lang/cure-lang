%default total

data OpticKind = LensKind | AffineKind | TraversalKind

data Pair a = MkPair a a

FocusShape : OpticKind -> Type -> Type
FocusShape LensKind a = Maybe a
FocusShape AffineKind a = Pair a
FocusShape TraversalKind a = Maybe a

mkLens : a -> FocusShape LensKind a
mkLens x = Just x

mkAffine : a -> FocusShape AffineKind a
mkAffine x = MkPair x x
