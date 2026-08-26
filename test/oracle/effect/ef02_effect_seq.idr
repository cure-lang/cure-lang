%default total

%foreign "scheme:blodwen-new-ref"
prim__mkref : PrimIO Int

mkref : IO Int
mkref = fromPrim prim__mkref

%foreign "scheme:blodwen-abs"
prim__abs : Int -> PrimIO Int

eff_abs : Int -> IO Int
eff_abs n = fromPrim (prim__abs n)

act : IO Int
act = do
  x <- mkref
  eff_abs x
