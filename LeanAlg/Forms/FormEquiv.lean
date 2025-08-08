import Mathlib

variable {k V V₁ V₂ V₃ : Type} [Field k]
         [AddCommGroup V] [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
         [Module k V] [Module k V₁] [Module k V₂] [Module k V₃]

open LinearMap
open LinearMap (BilinForm)

structure BilinIsometry {k V₁ V₂ : Type} [Field k]
         [AddCommGroup V] [AddCommGroup V₁] [AddCommGroup V₂]
         [Module k V] [Module k V₁] [Module k V₂]
         (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂) extends V₁ →ₗ[k] V₂ where
  compat : ∀ v w:V₁, β₁ v w = β₂ (toFun v) (toFun w)

notation:100 lhs:100 "→[" field:100 "," lhb:100 "," 
  rhb:100 "]" rhs:100 => 
  BilinIsometry (k := field) (V₁ := lhs) (V₂ := rhs) lhb rhb  


structure BilinIsomEquiv {k V₁ V₂ : Type} [Field k]
         [AddCommGroup V₁] [AddCommGroup V₂]
         [Module k V₁] [Module k V₂]
         (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂) extends V₁ ≃ₗ[k] V₂ where
  compat : ∀ v w:V₁, β₁ v w = β₂ (toFun v) (toFun w)
  
notation:100 lhs:100 "≃[" field:100 "," lhb:100 "," 
  rhb:100 "]" rhs:100 => 
  BilinIsomEquiv (k := field) (V₁ := lhs) (V₂ := rhs) lhb rhb  

namespace BilinIsomEquiv 

def Symm (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂)
    (h : V₁≃[k,β₁,β₂]V₂) :
  V₂ ≃[k,β₂,β₁] V₁ := 
  { LinearEquiv.symm (toLinearEquiv h) with 
    compat := by 
      intro _ _
      rw [ h.compat ]
      simp
  }

def Trans (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂) (β₃ : BilinForm k V₃)
    (h₁₂ : V₁≃[k,β₁,β₂]V₂) (h₂₃ : V₂≃[k,β₂,β₃]V₃) :
  V₁≃[k,β₁,β₃]V₃ 
  :=
  { LinearEquiv.trans (toLinearEquiv h₁₂) (toLinearEquiv h₂₃) with
    compat := by 
      intro _ _ 
      rw [ h₁₂.compat, h₂₃.compat ]
      simp
  }     

end BilinIsomEquiv
