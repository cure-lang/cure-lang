%default total

data Color = Red | Green | Blue

data Box = Mk Color

f : Color -> Box
f c = case Mk c of
        Mk Red => Mk Blue
        other => other
