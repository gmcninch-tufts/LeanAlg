import Mathlib

variable {α : Type} [DecidableEq α]

structure Edge (α : Type) [DecidableEq α] where
  endpoints : Multiset α
  pf : Multiset.card endpoints = 2

example : Edge ℕ := Edge.mk {1,1} (by norm_num)
example : Edge ℕ := Edge.mk {1,2} (by norm_num)

-- maybe easier way of constructing an edge

def mkendpoint (a b : α) : Edge α :=
  Edge.mk {a,b} (by norm_num)

example : Edge ℕ := mkendpoint 1 1

def incident (e : Edge α) (a : α) : Prop :=
  a ∈ e.endpoints

structure graph (α : Type) [DecidableEq α] where
  vertices : Finset α
  edges : Finset (Edge α)
  p : ∀ e ∈ edges, (Multiset.toFinset e.endpoints) ⊆ vertices
