import Mathlib

open Polynomial
open TensorProduct

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace PolynomialModule

/--
For a polynomial `f:R[X]`, and an R-module M, multiplication
by f determines an R-module homomorphism `M →ₗ[R] PolynomialModule R M`
-/
def MulByPolynomial (f : R[X]) : M →ₗ[R] PolynomialModule R M :=
  (DistribMulAction.toModuleEnd R[X] (PolynomialModule R M) f) ∘ₗ
    (PolynomialModule.lsingle R 0)

/-- The bilinear mapping `R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M`
given by the rule `f ↦ m ↦ (MulByPolynomial f) m`
-/
def Pairing (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M where
  toFun :=  MulByPolynomial
  map_add' f g := by
    ext
    rw [ MulByPolynomial, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply ]
    exact  add_smul f g _
  map_smul' t f := by
    rw [ RingHom.id_apply ]
    ext
    unfold MulByPolynomial
    simp 

/--
There is a `R[X]`-linear mapping `R[X] ⊗[R] M → PolynomialModule R M`
build from the bilinear mapping `BilinToPolyMod` `TensorProduct.lift`.

The mapping property of the tensor product gives the underyling
`R`-linear mapping, which is then confirmed to be `R[X]`-linear using
`TensorProduct.induction_on`
-/
def TensorMap (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    R[X] ⊗[R] M →ₗ[R[X]] PolynomialModule R M := 
  let φ : R[X] ⊗[R] M →ₗ[R] PolynomialModule R M := lift (Pairing R M)
  { toFun := φ.toFun,
    map_add' := φ.map_add,
    map_smul' := by
      intro g x
      rw [ RingHom.id_apply
         , AddHom.toFun_eq_coe
         , LinearMap.coe_toAddHom ]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul h y =>
          unfold φ
          rw [ smul_tmul', lift.tmul, lift.tmul , smul_eq_mul ]
          simp only [Pairing, MulByPolynomial, LinearMap.coe_mk,
            AddHom.coe_mk ]
          rw [ LinearMap.comp_apply, LinearMap.comp_apply ]
          simp only [DistribMulAction.toModuleEnd_apply,
            LinearMap.coe_restrictScalars, DistribMulAction.toLinearMap_apply]
          rw [ ←smul_eq_mul, smul_assoc ]
      | add x y hx hy =>
          rw [ smul_add, map_add, map_add, smul_add ]
          rw [ hx ,hy ]
    }

/-- There is an `R[X]` linear equivalence `(R[X] ⊗[R] M) ≃ₗ[R[X]]
   (PolynomialModule R M)` The `toFun` is given by
   `TensorMap`. The `left_inv` and `right_inv` conditions are proved
   using `TensorProduct.induction_on`, `Polynomial.induction_on` and
   `PolynomialModule.induction_on`
-/
def TensorProductEquivPolynomialModule : (R[X] ⊗[R] M) ≃ₗ[R[X]] (PolynomialModule R M) :=
  let incl : ℕ → M →ₗ[R] R[X] ⊗[R] M := fun n =>
    TensorProduct.mk R R[X] M (monomial n 1)
  { toFun := (TensorMap R M).toFun

    map_add' := (TensorMap R M).map_add

    map_smul' := (TensorMap R M).map_smul

    invFun := Finsupp.lsum R incl

    left_inv := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul h y  =>
          simp only [TensorMap, PolynomialModule.Pairing, MulByPolynomial,
                     AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
                     AddHom.coe_mk, lift.tmul, LinearMap.coe_mk
                     ]
          rw [ LinearMap.comp_apply ]
          induction h using Polynomial.induction_on' with
          | add p q hp hq =>
              rw [ add_tmul ]
              simp_all only [DistribMulAction.toModuleEnd_apply, 
                LinearMap.coe_restrictScalars,
                DistribMulAction.toLinearMap_apply, incl ]
              rw [add_smul]
              rw [←hp, ←hq]
              simp only [map_add]
          | monomial j t =>
              simp only [DistribMulAction.toModuleEnd_apply, 
                LinearMap.coe_restrictScalars,
                DistribMulAction.toLinearMap_apply]
              rw [Finsupp.lsum_apply R incl]
              have : ((monomial j) t • (PolynomialModule.lsingle R 0) y)
                  = (PolynomialModule.lsingle R j) (t • y) := by
                refine PolynomialModule.monomial_smul_single (M := M) j t 0 y
              rw [this]
              
              have pm_sum_lsingle_index {z : M}
                  {g : ℕ → M → R[X] ⊗[R] M} (hg : g j 0 = 0) :
                  Finsupp.sum ((PolynomialModule.lsingle R j) z) g = g j z := by
                apply Finsupp.sum_single_index ?_
                · exact hg
              rw [pm_sum_lsingle_index (z := t•y) (by simp only [map_zero])]
              unfold incl
              simp only [mk_apply] --simp only [map_smul, mk_apply]
              rw [Polynomial.smul_monomial] --rw [TensorProduct.smul_tmul', Polynomial.smul_monomial]
              simp only [smul_eq_mul, mul_one]

      | add w₁ w₂ hw₁ hw₂ =>
          rw [ (TensorMap R M).map_add' w₁ w₂ ]
          rw [ map_add ]
          rw [ hw₁, hw₂ ]

    right_inv := by
      intro v
      induction v using PolynomialModule.induction_linear with
      | zero => simp
      | add w₁ w₂ hw₁ hw₂ =>
          rw [ map_add ]
          rw [ (TensorMap R M).map_add' ]
          rw [ hw₁, hw₂ ]
      | single j x =>
          simp only [TensorMap, PolynomialModule.Pairing]
          rw [Finsupp.lsum_apply R incl]
          have pm_sum_single_index {z : M}
              {g : ℕ → M → R[X] ⊗[R] M} (hg : g j 0 = 0) :
              Finsupp.sum ((PolynomialModule.single R j) z) g = g j z :=  by
            apply Finsupp.sum_single_index ?_
            · exact hg
          rw [pm_sum_single_index (by simp)]
          simp_all only [MulByPolynomial, DistribMulAction.toModuleEnd_apply, mk_apply, 
            AddHom.toFun_eq_coe, lift.tmul',
            LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars, 
            Function.comp_apply, DistribMulAction.toLinearMap_apply, incl]
          have monomial_smul_lsingle (j : ℕ) (r : R) (k : ℕ) (m : M) :
              (Polynomial.monomial j) r • (PolynomialModule.lsingle R k) m =
              (PolynomialModule.lsingle R (j + k)) (r • m) := by
            apply PolynomialModule.monomial_smul_single
          rw [monomial_smul_lsingle j 1 0 x]
          simp only [add_zero, one_smul]
          rfl
   }

end


