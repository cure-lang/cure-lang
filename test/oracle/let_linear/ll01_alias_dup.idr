%default total
data Box = MkBox
data Widget = MkWidget
data Pair = MkPair Box Box
data WPair = MkWPair Widget Widget
consume : (1 _ : Box) -> Widget
consume MkBox = MkWidget
f : (1 _ : Box) -> Pair
f c = let x = c in MkPair x x
