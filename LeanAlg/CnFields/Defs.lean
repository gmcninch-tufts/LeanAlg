import Mathlib

universe μ ν 

variable (k : Type μ) [Field k]

def IsCr (r : ℕ) : Prop :=
  ∀ (n : ℕ),
  ∀ f : MvPolynomial (Fin n) k, 
  ∀ {d : ℕ},
  MvPolynomial.IsHomogeneous f d → d^r < n → 
  ∃ v  : Fin n → k, f.eval v = 0 ∧ v ≠ 0

def IsC1 : Prop := IsCr k 1

theorem finext_c1_of_c1 (L : Type μ) [Field L] [Algebra k L]
        [FiniteDimensional k L] (h : IsC1 k) :
  IsC1 L := by
  sorry


example : CSA k := CSA.mk (AlgCat.of k k)

def CSA.of (A : Type ν) [Ring A] [Algebra k A]
  [Algebra.IsCentral k A] [IsSimpleRing A] [FiniteDimensional k A] :
  CSA k :=
  CSA.mk (AlgCat.of k A)

#check CSA.of k

#check IsBrauerEquivalent

#check CSA.mk 

theorem csa_trivial_of_c1 (h : IsC1 k) (A : CSA k) :
  IsBrauerEquivalent A (CSA.of k k) := by sorry


--------------------------------------------------------------------------------

-- theorem (L : Type μ) [Field L] [Algebra k L]
--         [FiniteDimensional k L] (h : IsC1 k) 

def foo (ι τ : Type μ) : (ι → τ → k) ≃ ((ι × τ) → k) where
  toFun := fun M => (fun ⟨i,j⟩ => M i j)
  invFun := fun N => (fun i => fun j => N ⟨i,j⟩)
  left_inv := by 
    intro M
    ext i j
    simp
  right_inv := by 
    intro N
    ext ⟨i,j⟩
    simp
    
def foo' (ι τ : Type μ) : (ι → τ → k) ≃ ((ι × τ) → k) where
  toFun := Function.uncurry
  invFun := Function.curry
  left_inv := by exact congrFun rfl
  right_inv := by exact congrFun rfl
    
    
  

example (n : ℕ) (f : MvPolynomial (Fin n × Fin n) k) : Matrix (Fin n) (Fin n) k → k :=
  fun M => f.eval₂ (RingHom.id k) (Function.uncurry M)
  
@[simp]
noncomputable
def M (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  fun i j => MvPolynomial.X ⟨i,j⟩
  
example : (M k 1).det = MvPolynomial.X (0,0) := by 
  simp_all only [Matrix.det_unique, Fin.default_eq_zero, Fin.isValue, M]

example : (M k 2).det = MvPolynomial.X (0,0) * MvPolynomial.X ⟨1,1⟩ -  
                        MvPolynomial.X ⟨0,1⟩ * MvPolynomial.X ⟨1,0⟩ := by 
                            


