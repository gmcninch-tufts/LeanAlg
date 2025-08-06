
import Mathlib.Tactic

import Mathlib.Data.Vector.Defs
import Mathlib.Data.Rat.Defs

variable (d : ℕ)

def Qvs (d :ℕ) : Type :=  Vector ℚ d

#check Qvs

def QvsBasis : (d :ℕ) -> Vector (Qvs d) d := sorry

#eval (1/2 : ℚ).den

#eval (1/7:ℚ) + (1/37)

example : (1:ℤ) + 1 = 2 := by 
  simp

example : (2/14:ℚ) = 1/7 := by
 simp

example :(1/2 : ℚ) + (3/7 : ℚ) = 4/14 := by 
 simp


--example (v w : Qvs 3) : Qvs 3 := v + w
