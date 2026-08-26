%default total

sym' : {0 a : Type} -> {0 x : a} -> {0 y : a} -> x = y -> y = x
sym' Refl = Refl
