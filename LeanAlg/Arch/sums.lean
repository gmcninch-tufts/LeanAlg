
import Mathlib.Tactic

open BigOperators
open Finset


variable {α : Type*} [Field α] {r : α} {n : ℕ}

theorem geometric_sum (h:r ≠ 1) : ∑ j ∈ range (n+1), r^j = ( r^(n+1) - 1 )/(r - 1) := by
  have hn : r - 1 ≠ 0 := by 
    exact sub_ne_zero_of_ne h

  apply (mul_right_inj' hn).mp
  
  have distribute (n:ℕ): r * ∑ j ∈ range n, r^j = ∑ j ∈ range n, r^(j + 1) := by 
    have h  (i:ℕ) : r*r^i = r^(i+1) := by ring
    rw [ Finset.mul_sum ]
    apply Finset.sum_congr rfl 
    intro x _
    exact h x
  
  have : (r - 1) * ∑ j ∈ range (n+1), r^j = r^(n+1) - 1 := by
    rw [ sub_mul, distribute, sum_range_succ, one_mul, sum_range_succ' ]
    ring

  rw [ this ]
  rw [ mul_div_cancel₀ (r ^ (n + 1) - 1) hn ] 
  

