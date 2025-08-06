import Mathlib.Tactic

open Lattice
variable (α:Type) [CompleteLattice α] (a:α)

example  (S : Set α) ( h : a ∈ S) : sInf S ≤ a:= by
  apply sInf_le
  assumption  


-- this is called `bot_le`
example : ⊥ ≤ a := by
  rw [ ← sSup_empty ]
  apply sSup_le 
  rintro b h
  exfalso
  exact h
