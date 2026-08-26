%default total

data OpticKind = LensKind | AffineKind | TraversalKind

FocusShape : OpticKind -> Type
FocusShape LensKind = Unit
FocusShape AffineKind = Bool
FocusShape TraversalKind = Unit

mkLens : FocusShape LensKind
mkLens = ()

okAffine : FocusShape AffineKind
okAffine = True
