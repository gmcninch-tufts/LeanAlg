
import Mathlib.Tactic

import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Data.Vector.Zip

variable (k:Type) [ Field k ] [Fintype k]

--example (k:Type) [Field k] [Fintype k] (p:ℕ) [Fact isPrime p]:  := ModZ p

open scoped Classical
open Equiv
open Subgroup


#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]

#simp [mul_assoc] c[(1 : Fin 4),2,3,4]


#check Prod.casesOn


#check Sort
#check Type
#check Prop

instance {a: Type} [Add a] {n:ℕ} : Add (Vector a n) where
  add x y := Vector.zipWith (λ a b => a + b) x y 

open Vector

def aa : Vector ℕ 3 := 3 ::ᵥ 8 ::ᵥ 11 ::ᵥ nil --Vector.cons 1 nil

#eval aa + aa

#eval (2: ZMod 13) * (-5: ZMod 13) 


example (x : ZMod p) [Fact (Nat.Prime p)] (nz : ¬ x = 0) :  x * x⁻¹ = 1:= by
  exact mul_inv_cancel nz
 

--example 
  


example (D:Type) [DivisionRing D] (a:D) (h:¬ a = 0) : a*a⁻¹ = 1 := mul_inv_cancel h 

#check mul_inv_cancel 
