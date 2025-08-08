import Mathlib

variable { k : Type } [Field k]
variable { V : Type } [AddCommGroup V] [Module k V] [BEq V]
variable { W : Type } [AddCommGroup W] [Module k W] [BEq V]

--def T : Type := TensorProduct k V W 

open scoped TensorProduct

noncomputable
example (x y : V ⊗[k] W) : V ⊗[k] W := x + y



example (v w : V) : V := v + w
