%default total
data Box = MkBox
data Widget = MkWidget
data Pair = MkPair Box Box
data WPair = MkWPair Widget Widget
consume : (1 _ : Box) -> Widget
consume MkBox = MkWidget
f : (1 _ : Box) -> WPair
f c = let x = consume c in MkWPair x x
