%default total

-- Literal members as case sentinels. Idris2 models this as a named enum; Cure
-- writes the inhabitants directly in type position (`:north | :south`) and the
-- elaborator derives the enum.
data Dir = North | South

dir : Dir -> Int
dir North = 0
dir South = 1

go : Int
go = dir North
