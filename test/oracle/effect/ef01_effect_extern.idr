%default total

%foreign "scheme:blodwen-thread"
prim__yield : PrimIO ()

sched_yield : IO ()
sched_yield = fromPrim prim__yield

act : IO ()
act = sched_yield
