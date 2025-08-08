import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings


namespace PolyEquiv
open Polynomial
open TensorProduct

noncomputable section

variable {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]

/--
For a polynomial `f:R[X]`, and an R-module M, multiplication
by f determines an R-module homomorphism `M →ₗ[R] PolynomialModule R M`
--/
def MulByPoly (f:R[X]) : M →ₗ[R] PolynomialModule R M where
  toFun := fun m => f • (PolynomialModule.single R 0 m)
  map_add' := by simp
  map_smul' := by
    intro t m
    rw [ PolynomialModule.single_smul
       , smul_comm
       , RingHom.id_apply ]

/-- The bilinear mapping `R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M`
given by the rule `f ↦ m ↦ (MulByPoly f) m`
--/
def BilinToPolyMod (R M:Type*) [CommRing R] [AddCommGroup M] [Module R M] :
   R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M where
   toFun :=  MulByPoly
   map_add' f g := by
     ext
     rw [MulByPoly, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
     exact  add_smul f g _
   map_smul' t f := by
     rw [ RingHom.id_apply ]
     ext
     unfold MulByPoly
     simp only [ LinearMap.coe_mk, AddHom.coe_mk,
                 smul_assoc,  LinearMap.smul_apply ]

/--
There is a `R[X]`-linear mapping `R[X] ⊗[R] M → PolynomialModule R M`
determined (via `TensorProduct.lift`) by the bilinear mapping `BilinToPolyMod`

The mapping property of the tensor product gives the underyling
`R`-linear mapping, which is then confirmed (using
`TensorProduct.induction_on`) to be `R[X]`-linear.
--/
def TensorMap (R M:Type*) [CommRing R] [AddCommGroup M] [Module R M]  :
  R[X] ⊗[R] M →ₗ[R[X]] PolynomialModule R M := by
  let φ : R[X] ⊗[R] M →ₗ[R] PolynomialModule R M := lift (BilinToPolyMod R M)
  exact
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
            simp only [BilinToPolyMod, MulByPoly, LinearMap.coe_mk, AddHom.coe_mk ]
            rw [ ←smul_eq_mul, smul_assoc]
        | add x y hx hy =>
            rw [ smul_add, map_add, map_add, smul_add ]
            rw [ hx ,hy ]
    }



/-- apply `Finsupp.sum_single_index` on PolynomialModule.single
--/
lemma pm_sum_single_index {N:Type*} [AddCommGroup N] [Module R N] {m:ℕ} {y:M}
  {g:ℕ → M → N} (hg : g m 0 = 0):
  Finsupp.sum ((PolynomialModule.single R m) y) g = g m y :=  by
  apply Finsupp.sum_single_index
  · exact hg

/-- There is an `R[X]` linear equivalence `(R[X] ⊗[R] M) ≃ₗ[R[X]]
   (PolynomialModule R M)` The `toFun` construction comes from
   `TensorMap`. The `left_inv` and `right_inv` conditions are proved
   using `TensorProduct.induction_on`, `Polynomial.induction_on` and
   `PolynomialModule.induction_on`
--/
def PolynomialModuleEquivTensorProduct  :
 (R[X] ⊗[R] M) ≃ₗ[R[X]] (PolynomialModule R M) := by
 let incl : ℕ → M →+ R[X] ⊗[R] M := by
   intro n
   exact
    {
      toFun := fun x => monomial n 1 ⊗ₜ[R] x
      map_zero' := by simp
      map_add' m₁ m₂ := tmul_add _ m₁ m₂
    }

 let ψ : PolynomialModule R M →+ R[X] ⊗[R] M :=
    {
     toFun := fun v => v.sum fun n => (incl n).toFun
     map_zero' := by simp
     map_add' := (Finsupp.liftAddHom incl).map_add
    }

 exact
 { toFun := (TensorMap R M).toFun

   map_add' := (TensorMap R M).map_add

   map_smul' := (TensorMap R M).map_smul

   invFun := ψ

   left_inv := by
     intro x
     induction x using TensorProduct.induction_on with
     | zero => simp
     | tmul h y  =>
        simp only [TensorMap, BilinToPolyMod, MulByPoly,
                   AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
                   AddHom.coe_mk, lift.tmul, LinearMap.coe_mk
                   ]
        induction h using Polynomial.induction_on' with
        | add p q hp hq =>
           rw [ add_smul ]
           unfold ψ; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
           unfold ψ at hp; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hp
           unfold ψ at hq; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hq
           rw [ Finsupp.sum_add_index (h_zero := by simp) ]
           · rw [ hp, hq ]
             rw [ add_tmul ]
           · intro _ _ b₁ b₂
             exact tmul_add _ b₁ b₂
        | monomial m t =>
           rw [ PolynomialModule.monomial_smul_single  ]
           rw [add_zero]
           unfold ψ; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
           rw [ pm_sum_single_index ( hg := by apply tmul_zero ) ]
           simp only [ tmul_smul, incl ]
           rw [ TensorProduct.smul_tmul' ]
           rw [ Polynomial.smul_monomial t m 1 ]
           rw [ smul_eq_mul, mul_one ]

     | add w₁ w₂ hw₁ hw₂ =>
        rw [ (TensorMap R M).map_add' w₁ w₂ ]
        rw [ ψ.map_add ]
        rw [ hw₁, hw₂ ]

   right_inv := by
     intro v
     induction v using PolynomialModule.induction_linear with
     | zero => simp
     | add w₁ w₂ hw₁ hw₂ =>
       rw [ ψ.map_add ]
       rw [ (TensorMap R M).map_add' ]
       rw [ hw₁, hw₂ ]
     | single m t =>
       unfold ψ
       simp only [TensorMap, BilinToPolyMod, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
         ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
         AddHom.coe_mk]
       rw [ pm_sum_single_index  ]
       unfold MulByPoly
       simp only [incl, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk,
         PolynomialModule.monomial_smul_single, add_zero, one_smul]
       apply map_zero
   }

end
end PolyEquiv
