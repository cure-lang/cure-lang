import Data.So

%default total

leftIntro : So (True || False)
leftIntro = orSo {a=True} {b=False} (Left Oh)
