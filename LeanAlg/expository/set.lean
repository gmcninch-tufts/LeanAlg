import Mathlib

example : ({ 1,2} : Set ℕ) ≠ {3,4} := by 
  grind


example : 3 ∉ ({1,2} : Set ℕ) := by simp
