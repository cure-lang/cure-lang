%default total

data N = Z | S N

data Vec : Type -> N -> Type where
  VNil : Vec a Z
  VCons : (k : N) -> a -> Vec a k -> Vec a (S k)

onlyNil : Vec N Z -> N
onlyNil VNil impossible
