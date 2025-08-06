import Mathlib.Tactic


variable (L:Type) [ Field L ]

variable (K₁ K₂ : Subfield L)

example : Subfield L := K₁ ⊔ K₂

example : (K₁ ⊓ K₂).carrier = K₁.carrier ⊓ K₂.carrier := by
  simp

instance : Fact (Nat.Prime 317) where
 out := by norm_num

example : ¬ ((L:Type) → [Field L]  → (K₁ K₂ : Subfield L) → 
  (K₁ ⊔ K₂).carrier = K₁.carrier ⊔ K₂.carrier) := by
  intro h
  let p := 317
  let L := GaloisField p 6
  let K₁ := GaloisField p 2
  let K₂ := GaloisField p 3         

--def pp : Instance 

def ff : Fact (Nat.Prime 5) := Fact.mk (by norm_num)

instance  : Fact (Nat.Prime 5) where 
  out := by norm_num


example : Type := GaloisField 5 6 

example : Fact (Nat.Prime 13) := 
  Fact.mk (by norm_num)

example : Fact (Nat.Prime 13) := by
  apply fact_iff.mpr
  norm_num

  
