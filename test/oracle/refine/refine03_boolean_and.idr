import Data.So

%default total

splitLeft : So (True && True) -> So True
splitLeft x = case soAnd {a=True} {b=True} x of (l, _) => l
