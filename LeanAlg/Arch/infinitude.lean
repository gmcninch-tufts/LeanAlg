import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finsupp.Defs

open Nat

theorem infinitude_of_primes : ∀ N:ℕ, ∃ p>N, Nat.Prime p := by 
  intro N
  let M:ℕ := N.factorial  + 1

  let p:ℕ := Nat.minFac M

  have h0 : Nat.Prime p := by
    refine Nat.minFac_prime ?n1
    have h : N.factorial > 0 := by
      exact Nat.factorial_pos N
    unfold M  
    linarith

  use p
  apply And.intro
  
  case h.left =>
    by_contra h 
    have h1 : p ∣ Nat.factorial N + 1 := by exact minFac_dvd M
    have h2 : p ∣ Nat.factorial N := by
      refine dvd_factorial ?pos ?lt
      case pos => exact minFac_pos M
      case lt => exact Nat.le_of_not_lt h
    have : p ∣ 1 := (Nat.dvd_add_iff_right h2).mpr h1
    exact Nat.Prime.not_dvd_one h0 this
  
  case h.right =>
    exact h0
   
    
      
  
