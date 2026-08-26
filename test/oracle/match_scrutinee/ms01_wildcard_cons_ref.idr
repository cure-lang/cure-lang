%default total

data Box a = MkBox a

cyc : List t -> Box (List t)
cyc list = case list of
                []        => MkBox []
                (_ :: _)  => MkBox list
