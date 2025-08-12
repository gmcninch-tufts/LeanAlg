import Mathlib

universe u v

variable {k : Type u} [Field k]

variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

structure RegularFunction (k : Type u) (V : Type v) [Field k] [AddCommGroup V]
   [Module k V] [FiniteDimensional k V] where
  f : (ι : Type) → (b : Module.Basis ι k V) → MvPolynomial ι k 
  
def eval (f:RegularFunction k V) (v : V) {ι:Type} (B : Module.Basis ι k V)




