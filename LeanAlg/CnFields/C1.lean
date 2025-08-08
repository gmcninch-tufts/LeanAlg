import Mathlib

def IsC1 (k : Type) [Field k] : Prop :=
  ∀ (n : ℕ),
  ∀ f : MvPolynomial (Fin n) k, 
  ∀ {d : ℕ},
  MvPolynomial.IsHomogeneous f d → d < n → 
  ∃ v  : Fin n → k, f.eval v = 0 ∧ v ≠ 0
