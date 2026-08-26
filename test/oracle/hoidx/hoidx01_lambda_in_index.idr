%default total

data Dec = D0 | D1

data Eff = Pure Dec | Bind Dec (Dec -> Eff)

bind : Eff -> (Dec -> Eff) -> Eff
bind (Pure x) f = f x
bind (Bind e g) f = Bind e (\y => bind (g y) f)

reflBind : (m : Eff) -> bind m (\y => Pure y) = bind m (\y => Pure y)
reflBind m = Refl
