
import Mathlib.Tactic
import Mathlib.Algebra.CharP.Basic

variable (F : Type) [Field F] [CharP F 3]
variable (a b c d: F)

example (F : Type) [Field F] (p:ℕ) [Fact (Nat.Prime p)] [CharP F p] : (p:F) = 0 := by
  have := CharP.cast_eq_zero F (p:ℕ)
  exact this


theorem pZero  (F : Type) [Field F] (p:ℕ) [Fact (Nat.Prime p)] [CharP F p] (a:F) : p*a = 0:= by
  have := CharP.cast_eq_zero F (p:ℕ)
  simp
  


example : a + a + a = 0:= by
  have h : a + a + a = 3*a := by ring
  rw [h]
  exact pZero F 3 a  
  
