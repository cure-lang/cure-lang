%default total

data Box a = MkBox a

cyc : List t -> Box (List t)
cyc list = case list of
                []        => MkBox []
                (h :: t)  => MkBox list
