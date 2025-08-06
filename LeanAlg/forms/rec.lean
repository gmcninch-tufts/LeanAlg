import Mathlib

variable (ι : Type) (X : ι → Type)

example ( x : (i : ι) → X i) (i j : ι) (h : i = j) : X i := if i = j then x j else x i 


