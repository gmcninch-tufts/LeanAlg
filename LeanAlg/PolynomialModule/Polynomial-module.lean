import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings


namespace PolyEquiv
open Polynomial
open TensorProduct

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/--
For a polynomial `f:R[X]`, and an R-module M, multiplication
by f determines an R-module homomorphism `M →ₗ[R] PolynomialModule R M`
-/
def MulByPoly (f : R[X]) : M →ₗ[R] PolynomialModule R M :=
    (DistribMulAction.toModuleEnd R[X] (PolynomialModule R M) f) ∘ₗ
       (PolynomialModule.lsingle R 0)

/-- The bilinear mapping `R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M`
given by the rule `f ↦ m ↦ (MulByPoly f) m`
-/
def PolynomialModule.Pairing (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
     R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M where
   toFun :=  MulByPoly
   map_add' f g := by
     ext
     rw [ MulByPoly, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply ]
     exact  add_smul f g _
   map_smul' t f := by
     rw [ RingHom.id_apply ]
     ext
     unfold MulByPoly
     simp_all only [LinearMap.smul_apply, DistribMulAction.toModuleEnd_apply, 
       LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, 
       DistribMulAction.toLinearMap_apply, smul_assoc]

open PolynomialModule in
/--
There is a `R[X]`-linear mapping `R[X] ⊗[R] M → PolynomialModule R M`
determined (via `TensorProduct.lift`) by the bilinear mapping `BilinToPolyMod`

The mapping property of the tensor product gives the underyling
`R`-linear mapping, which is then confirmed (using
`TensorProduct.induction_on`) to be `R[X]`-linear.
-/
def TensorMap (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    R[X] ⊗[R] M →ₗ[R[X]] PolynomialModule R M := 
  let φ : R[X] ⊗[R] M →ₗ[R] PolynomialModule R M := lift (PolynomialModule.Pairing R M)
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
          simp only [PolynomialModule.Pairing, MulByPoly, LinearMap.coe_mk,
            AddHom.coe_mk ]
          rw [ LinearMap.comp_apply, LinearMap.comp_apply ]
          simp only [DistribMulAction.toModuleEnd_apply,
            LinearMap.coe_restrictScalars, DistribMulAction.toLinearMap_apply]
          rw [ ←smul_eq_mul, smul_assoc ]
      | add x y hx hy =>
          rw [ smul_add, map_add, map_add, smul_add ]
          rw [ hx ,hy ]
    }

/-- apply `Finsupp.sum_single_index` on PolynomialModule.lsingle
-/
lemma pm_sum_lsingle_index' {N : Type*} [AddCommGroup N] [Module R N] {j : ℕ} {y : M}
    {g : ℕ → M → N} (hg : g j 0 = 0) :
    Finsupp.sum ((PolynomialModule.lsingle R j) y) g = g j y :=  by
  apply Finsupp.sum_single_index ?_
  · exact hg

/-- apply `Finsupp.sum_single_index` on PolynomialModule.single
-/
lemma pm_sum_single_index' {N : Type*} [AddCommGroup N] [Module R N] {j : ℕ} {y : M}
    {g : ℕ → M → N} (hg : g j 0 = 0) :
    Finsupp.sum ((PolynomialModule.single R j) y) g = g j y :=  by
  apply Finsupp.sum_single_index ?_
  · exact hg

lemma PolynomialModule.monomial_smul_lsingle' {R : Type u_1} {M : Type u_2}
    [CommRing R] [AddCommGroup M] [Module R M] (i : ℕ) (r : R) (j : ℕ) (m : M) :
    (Polynomial.monomial i) r • (PolynomialModule.lsingle R j) m =
    (PolynomialModule.lsingle R (i + j)) (r • m) := by
  apply PolynomialModule.monomial_smul_single

/-- There is an `R[X]` linear equivalence `(R[X] ⊗[R] M) ≃ₗ[R[X]]
   (PolynomialModule R M)` The `toFun` construction comes from
   `TensorMap`. The `left_inv` and `right_inv` conditions are proved
   using `TensorProduct.induction_on`, `Polynomial.induction_on` and
   `PolynomialModule.induction_on`
-/
def PolynomialModuleEquivTensorProduct : (R[X] ⊗[R] M) ≃ₗ[R[X]] (PolynomialModule R M) :=
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
          simp only [TensorMap, PolynomialModule.Pairing, MulByPoly,
                     AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
                     AddHom.coe_mk, lift.tmul, LinearMap.coe_mk
                     ]
          rw [ LinearMap.comp_apply ]
          induction h using Polynomial.induction_on' with
          | add p q hp hq =>
              rw [ add_tmul ]
              -- unfold ψ at *
              simp_all only [DistribMulAction.toModuleEnd_apply, 
                LinearMap.coe_restrictScalars,
                DistribMulAction.toLinearMap_apply, incl ]
              rw [add_smul]
              rw [←hp, ←hq]
              simp only [map_add]
          | monomial j t =>
              simp only [DistribMulAction.toModuleEnd_apply, LinearMap.coe_restrictScalars,
                DistribMulAction.toLinearMap_apply]
              rw [Finsupp.lsum_apply R incl]
              have : ((monomial j) t • (PolynomialModule.lsingle R 0) y)
                  = (PolynomialModule.lsingle R j) (t • y) := by
                refine PolynomialModule.monomial_smul_single (M := M) j t 0 y
              rw [this]
              
              have pm_sum_lsingle_index {z : M}
                  {g : ℕ → M → R[X] ⊗[R] M} (hg : g j 0 = 0) :
                  Finsupp.sum ((PolynomialModule.lsingle R j) z) g = g j z :=  by
                apply Finsupp.sum_single_index ?_
                · exact hg
              rw [pm_sum_lsingle_index (z := t•y) (by simp only [map_zero])]
              
              · unfold incl
                simp only [map_smul, mk_apply]
                rw [TensorProduct.smul_tmul', Polynomial.smul_monomial]
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
          simp_all only [MulByPoly, DistribMulAction.toModuleEnd_apply, mk_apply, 
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
end PolyEquiv
