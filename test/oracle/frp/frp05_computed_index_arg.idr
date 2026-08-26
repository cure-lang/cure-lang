%default total

-- A computed index reduced in ARGUMENT position: `Seqg x y : G (dmeet DDec DDec)`
-- fed to `Need : G DDec -> G DCau` requires `dmeet DDec DDec` to reduce to `DDec`
-- where the argument is checked. Idris reduces it and accepts; faithful
-- transliteration of frp05_computed_index_arg.cure — accept/accept.

data Dec = DDec | DCau

dmeet : Dec -> Dec -> Dec
dmeet DDec DDec = DDec
dmeet _ _ = DCau

data G : Dec -> Type where
  Mkd  : G DDec
  Seqg : G d1 -> G d2 -> G (dmeet d1 d2)
  Need : G DDec -> G DCau

f : G DDec -> G DDec -> G DCau
f x y = Need (Seqg x y)
