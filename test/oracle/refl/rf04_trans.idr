%default total

trans' : {0 a : Type} -> {0 x : a} -> {0 y : a} -> {0 z : a} -> x = y -> y = z -> x = z
trans' Refl q = q
