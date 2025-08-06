import Mathlib.Tactic

variable (K : Type) [Field K] [Fintype K] (p : ℕ) [CharP K p] 

variable (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

class FiniteVS (K:Type) (V:Type) [Field K] [Fintype K] (p:ℕ) [CharP K p] [AddCommGroup V] extends 
        FiniteDimensional K V
        
        

{ K : Type } [Field K] [Fintype K] (p:ℕ) [CharP K p] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

#check Module.finrank K V

#check FiniteField.card K p


