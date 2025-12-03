import Mathlib

noncomputable section

universe μ ν ω

variable {R : Type μ} {M : Type ν} [CommRing R] [AddCommGroup M] [Module R M]

open BigOperators in
example (φ : M →ₗ[R] M) (I : Type) (f : I →₀ M) :
  φ ( ∑ i ∈ f.support, f i ) = ∑ i∈ f.support, φ (f i) := by
    simp_all only [map_sum]

open BigOperators in
example (I : Type) (f : I →₀ M) (p : M → Prop) (hadd : ∀ x y : M, p x → p y → p (x + y))
  (h0 : p 0) (hI : (i : I) → p (f i)) :
  p (∑ i ∈ f.support, f i) := by
    apply Finset.sum_induction f p hadd h0
    intro i _
    exact hI i

theorem SymmetricAlgebra.induction_basis [Module.Free R M] (σ : Type ω) [Fintype σ]
    (b : Module.Basis σ R M)
    {motive : SymmetricAlgebra R M → Prop}
    (algebraMap : ∀ r, motive (algebraMap R (SymmetricAlgebra R M) r))
    (basis : ∀ i, motive (ι R M (b i)))
    (unit : motive 0)
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (a : SymmetricAlgebra R M) : motive a :=
  have : ∀ x : M, motive (ι R M x) := fun x => by
    rw [ ← Module.Basis.sum_repr b x ]
    rw [ map_sum ]
    apply Finset.sum_induction
    case hom => exact add
    case unit => exact unit
    case base =>
      intro i _
      rw [ map_smul, Algebra.smul_def ]
      apply mul _ _
      case a => apply algebraMap 
      case a => apply basis
  SymmetricAlgebra.induction R M algebraMap this mul add a

@[simp]
def MvPolynomialToSymmetricAlgebra [Module.Free R M] (ι : Type ω) [Fintype ι]
    (b : Module.Basis ι R M) :
    MvPolynomial ι R  →ₐ[R]  SymmetricAlgebra R M :=
  { MvPolynomial.eval₂Hom (algebraMap R (SymmetricAlgebra R M)) (fun (i : ι) =>
      SymmetricAlgebra.ι R M (b i)) with
    commutes' := by simp_all
  }

@[simp]
def SymmetricAlgebraToMvPolynomial [Module.Free R M] (ι : Type ω) [Fintype ι]
    (b : Module.Basis ι R M) :
    SymmetricAlgebra R M →ₐ[R] MvPolynomial ι R :=
  have φ : M →ₗ[R] MvPolynomial ι R := b.constr R MvPolynomial.X

  { SymmetricAlgebra.lift φ with
    commutes' := by simp_all
  }

def SymmectricAlgebraEquivMvPolynomial [Module.Free R M] (σ : Type ω) [Fintype σ]
    (b : Module.Basis σ R M) :
    SymmetricAlgebra R M ≃ₐ[R] MvPolynomial σ R where
  toFun := SymmetricAlgebraToMvPolynomial σ b
  invFun := MvPolynomialToSymmetricAlgebra σ b
  left_inv := by
    intro f
    induction f using SymmetricAlgebra.induction_basis σ b with
    | algebraMap => simp
    | basis i =>
        simp    
        suffices h : (SymmetricAlgebra.ι R M) (b i) =
            (fun₀ | i => (1:R)) i • (SymmetricAlgebra.ι R M) (b i) by
          rw [ Finset.sum_eq_single i ]
          · simp
          · intro j hj hji
            rw [ Finsupp.single_eq_of_ne ]
            · simp
            · aesop
          · intro hi
            exfalso
            exact hi (Finset.mem_univ i)
        rw [ Finsupp.single_eq_same ]
        simp
    | unit => simp
    | mul f g mf mg =>
      sorry
    | add f g mf mg =>
      sorry
  right_inv := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C => simp
    | add => sorry
    | mul_X => sorry
  map_mul' := (SymmetricAlgebraToMvPolynomial σ b).map_mul
  map_add' := (SymmetricAlgebraToMvPolynomial σ b).map_add
  commutes' := by simp
