import Mathlib.Tactic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Util.Delaborators

set_option warningAsError false
open Set





variable (α:Type)
variable (S:Set α)

example (x : Set S) : Set S := x

example (x : α) : x ∈ (Set.univ : Set α) :=
  trivial


example (X Y : Set α) (h: X ⊂ Y) (hm : x ∈ X) : x ∈ Y := by
  rcases h with ⟨hs,_⟩
  exact hs hm

example (X Y : Set α) (h : X ⊂ Y) : ¬ (Y \ X) = ∅ := by 
  rintro k
  rcases h with ⟨_,hne⟩
  have he : Y ⊆ X := by
    intro y hy
    by_contra hx
    have diff : y ∈ Y \ X := ⟨ hy, hx ⟩
    rw [k] at diff
    exact diff
  exact hne he
  
      

example (X : Set α) (hx : x ∈ X) : ¬ X = ∅ := by
  intro h
  rw [h] at hx
  exact hx

 -- apply ne_of_mem_of_not_mem' hx



        
        
      
#check ne_of_mem_of_not_mem'
      




variable (X Y : Set α)
variable (h : X ⊂ Y)


--example (X : Set α)  (x: α) (hx : x ∈ X) : ¬ (x ∈ ∅) := by
--  exact?

#check (∅ :Set α)

--#example (X:Set α) (x:α) (hx : x ∈ X) : x ∈ (∅:Set α) := sorry

example (X:Set α) (x:α) (hx: x ∈ X) : x ∈ (univ : Set α) := trivial

example (x:α) : x ∈ (univ : Set α) := trivial

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

#check EmptyCollection


def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp
  apply Classical.em


example: 4 ∈ evens := by 
  rw [evens]
  simp
  exact Nat.even_iff.mpr rfl -- (Nat.instDecidablePredNatEvenInstAddNat.proof_1 4).mp rfl
  done


example : Even (18*379) := Nat.even_iff.mpr rfl

example : Odd (13*19*41) := Nat.odd_iff.mpr rfl

section mytype

variable (β:Type)

inductive BR (β:Type) := 
  | blue:β → BR β 
  | red: β → BR β

def red {β:Type} (x:BR β) := ∃ t, x = BR.red t

def blue {β:Type} (x: BR β) := ∃ t, x = BR.blue t

def reds {β:Type} : Set (BR β) := { x | red x }

def blues {β:Type} : Set (BR β) := { x | blue x }

example : reds ∪ blues = (univ:Set (BR β)) := by
  rw [ reds, blues ]
  ext x
  simp
  rcases x with xblue | xred
  right
  use xblue
  left
  use xred
  done

end mytype


#check Nat




example {α:Type} {s t u : Set α} : s ∩ t ∩ u = u ∩ t ∩ s := by 
  ext x
  simp [and_comm]
  done



example (p: Set β) (f:α → β) : Set α := f ⁻¹' p 



variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring
