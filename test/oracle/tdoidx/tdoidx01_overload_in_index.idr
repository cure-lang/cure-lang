%default total

-- E11 mirror: a name shared by two type-distinguished definitions, resolved by
-- argument type at a dependent-index use site. Cure spells this as a same-module
-- overload set; Idris2 spells the two members in sibling namespaces and resolves
-- the ambiguous reference by type. The occurrence sits in the type of `resolves`
-- (a propositional-equality index), the analogue of Cure's `Equivalent` index.

data Colour = Red | Green
data Box = MkB Colour
data Bag = MkG Colour

namespace B
  public export
  pick : Box -> Box -> Box
  pick a b = b

namespace G
  public export
  pick : Bag -> Bag -> Bag
  pick a b = b

resolves : pick (MkB Red) (MkB Green) = MkB Green
resolves = Refl
