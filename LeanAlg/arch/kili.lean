import Mathlib.Tactic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic 

variable (n:ℕ)

open Finset
open Nat

def foo : { n:ℕ // 2 ∣ n } → ℕ := by
  intro s
  exact ↑s

def foo2 (x:{ n:ℕ // 2∣n}) : ℕ := 
  ↑x

def bar : List { n:ℕ // 2 ∣ n} → List ℕ := by
  intro ls
  exact (List.map foo2 ls)

def product : List ℕ → ℕ := 
  fun (l:List ℕ) =>
    match l with
    | [] => 1
    | List.cons a as => a * product as

theorem prodEven  (l : List { n:ℕ // 2∣n })  (hl: l ≠ [])  : 2 ∣ (product $ (List.map foo2 l)) := by 
  match l with
   | List.cons x xs => sorry
  

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : 
   ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
    match n with
    | zero => simp
              --have hr : r-1 ≠ 0 := 
              --rw [ mul_left_cancel_of_ne_zero h]
              sorry
    | succ n => sorry


#check sub_self
#check add_left_cancel

example (c:ℝ) (h:r-c = 0) : r = c := by
  rw [←sub_self c] at h
  apply add_right_cancel at h
  assumption

def non_zero {r a: ℝ} (h:r ≠ a) : r - a ≠ 0 := by
  apply?
  -- intro _
  -- have k : r = a := by linarith
  -- exact h k

-- actually the previous result already turns out to be in mathlib...
#check sub_ne_zero_of_ne  

#check mul_left_cancel₀

example (a b r : ℝ) (h : r ≠ 1) : a/(r-1) = b/(r-1) → a = b := by
  intro k
  have l : r - 1 ≠ 0 := sub_ne_zero_of_ne h
  apply mul_right_cancel₀ l
  

#check eq_mul_of_div_eq
  
variable {F:Type} [Field F]

variable {c:F}

theorem recip_non_zero_of_non_zero (h:c ≠ 0) : 1/c ≠ 0 := by
  intro k
  have kk : c=0 := eq_zero_of_one_div_eq_zero k
  exact h kk

theorem cancel_denom  (a c : F) (h:c ≠ 0) : a/c*c = a := by 
  rw [div_eq_mul_inv]
  rw [mul_assoc]
  rw [mul_comm c⁻¹ c]
  rw [Field.mul_inv_cancel c h]
  ring

#check recip_non_zero_of_non_zero

example : ( h:c ≠ 0 ) →  1/c ≠ 0 := by 
  intro h
  exact (recip_non_zero_of_non_zero h)

example (a b c : F) (h : c ≠ 0): a/c = b/c → a = b := by
  intro l
  have h1 : 1/c ≠ 0 := by exact recip_non_zero_of_non_zero h
  have a1 : a*(1/c) = a/c := by ring
  have b1 : b*(1/c) = b/c := by ring
  have k1 : a*(1/c) = b*(1/c) := by 
    rw [a1,b1]
    assumption
  exact mul_right_cancel₀ h1 k1

example (a b c : F) (h : c ≠ 0): a/c = b/c → a = b := by
  intro l
  have k : a/c * c = b/c * c := by
    exact congr_arg (fun x  => x * c) l
  rw [ cancel_denom a c h ] at k
  rw [ cancel_denom b c h ] at k
  assumption

example (a b c:F) (h:a/c = b/c) : a*(1/c) = b*(1/c) := by
  have a1 : a*(1/c) = a/c := by ring
  have b1 : b*(1/c) = b/c := by ring
  rw [a1,b1]
  assumption


example (a b c:F) (h : a/c = b) : a = b*c := by
  have k: a/c*c = b*c := by exact congr_arg (fun x => x*c) h
  rw [ ← div_mul_cancel a c  ] at k

  


  
