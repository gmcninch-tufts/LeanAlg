import Mathlib

universe μ ν 

variable (ι : Type)
variable (k : Type) [Field k]
variable (V : Type) [AddCommGroup V] [Module k V]

#check (ι : Type) × (MvPolynomial ι k) × (Module.Basis ι k V)

#check Σ (ι : Type), (MvPolynomial ι k) × (Module.Basis ι k V)

def IsCr' (r : {q :ℚ // q≥0 }) : Prop :=
  ∀ (n : ℕ),
  ∀ f : MvPolynomial (Fin n) k, 
  ∀ {d : ℕ},
  MvPolynomial.IsHomogeneous f d → (d:ℝ) ^ (r:ℝ) < (n:ℝ) → 
  ∃ v  : Fin n → k, f.eval v = 0 ∧ v ≠ 0


--def RegularFunction (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
  
def PreRegularFunction (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]
  :  Type 1 :=
  Σ (ι : Type), (MvPolynomial ι k) × (Module.Basis ι k V)
  
def MvPolynomial.LinearChangeOfVar (k : Type) [Field k] (σ τ : Type) (φ : (σ →₀ k) ≃ₗ[k] τ →₀ k) :
  MvPolynomial σ k ≃ₐ[k] MvPolynomial τ k where
    toFun := _
    invFun := _
    left_inv := _
    right_inv := _
    map_mul' := _
    map_add' := _
    commutes' := _
  
inductive RegularFunction (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]
  
instance [AddCommGroup V] [Module k V] : Module k (RegularFunction k V) := by sorry
  
def RegularFunctionAssocPolynomial (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (ι : Type*) (b : Module.Basis ι k V)
  : RegularFunction k V ≃ MvPolynomial ι k := by sorry

def EvalRegularFunction (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]
  (f : RegularFunction k V) (v : V) : k := by sorry

def 

/- It would arguably be nice to replace `MvPolynomial` in the
  definition above with a coordinate-free version of homogeneous form.
  Arguably something like the following:
  
  - a definition of `RegularFunction` depending on `(k : Type*) (V :
    Type*) [Field k] [AddCommGroup V] [Module k V]`
	
	Types as follows:
	
	```
	def RegularFunctionAssocPolynomial (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
	  (f : RegularFunction k V) (ι : Type*) (b : Module.Basis ι k V)
      : MvPolynomial ι k := by sorry

	def EvalRegularFunction (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] 
      (f : RegularFunction k V) (v : V) : k := by sorry
	```
-/
