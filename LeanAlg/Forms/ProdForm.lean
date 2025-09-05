import Mathlib
import LeanAlg.Forms.Defs
import LeanAlg.Forms.FormEquiv

open LinearMap
open LinearMap (BilinForm)

variable {k V V₁ V₂ : Type} [Field k]
         [AddCommGroup V] [AddCommGroup V₁] [AddCommGroup V₂]
         [Module k V] [Module k V₁] [Module k V₂]

def ProductBilinForm (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂) : 
    BilinForm k (V₁ × V₂) :=
  let ψ₁ : BilinForm _ (V₁ × V₂) := 
    LinearMap.compl₁₂ 
      β₁
      (LinearMap.fst _ V₁ _)
      (LinearMap.fst _ V₁ _)
  let ψ₂ : BilinForm _ (V₁ × V₂) := 
    LinearMap.compl₁₂
      β₂
      (LinearMap.snd _ _ V₂)
      (LinearMap.snd _ _ V₂)
  ψ₁ + ψ₂ 

notation:100 lform:100 " ×b " rform:100 =>
  ProductBilinForm lform rform

@[simp]
theorem product_bilin_form_apply (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂)
    (x y : V₁ × V₂) :
  ProductBilinForm β₁ β₂ x y = (β₁ x.fst y.fst) + (β₂ x.snd y.snd) := by
    obtain ⟨fst, snd⟩ := x
    obtain ⟨fst_1, snd_1⟩ := y
    simp_all only
    rfl

theorem product_orthogonal (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂)
    (v₁ : V₁) (v₂ : V₂) :
  ProductBilinForm β₁ β₂ ⟨v₁,0⟩ ⟨0,v₂⟩ = 0 := by simp
  
def LinearMap.EpsilonSkew (β : BilinForm k V) (ε : k) : Prop :=
  ∀ x y, β x y = ε * β y x
  
theorem product_skew (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂) (ε : k)
    (h₁ : β₁.EpsilonSkew ε) (h₂ : β₂.EpsilonSkew ε) :
  (ProductBilinForm β₁ β₂).EpsilonSkew ε := by
  intro x y
  simp only [product_bilin_form_apply]
  rw [ h₁, h₂]
  ring

example (β : BilinForm k V) (W₁ W₂ : Subspace k V) : BilinForm k (W₁ × W₂) :=
  ProductBilinForm (BilinForm.restrict β W₁) (BilinForm.restrict β W₂)


noncomputable
def InternalDirSum (β : BilinForm k V) (W₁ W₂ : Subspace k V)
  (hc : IsCompl W₁ W₂)
  (ho : OrthogonalSubsets β W₁ W₂) : 
  (W₁ × W₂) ≃[k,(β.restrict W₁) ×b (β.restrict W₂),β] V :=
    { Submodule.prodEquivOfIsCompl W₁ W₂ hc with
      compat := by 
        rintro ⟨⟨x₁,hx₁⟩,⟨x₂,hx₂⟩⟩ 
        rintro ⟨⟨y₁,hy₁⟩,⟨y₂,hy₂⟩⟩
        simp_all only [OrthogonalSubsets, SetLike.mem_coe, product_bilin_form_apply,
          BilinForm.restrict_apply, domRestrict_apply, Submodule.coe_prodEquivOfIsCompl,
          AddHom.toFun_eq_coe, coe_toAddHom, coprod_apply, Submodule.subtype_apply, map_add,
          add_apply]           
        have z1 : β x₁ y₂ = 0 := (ho x₁ hx₁ y₂ hy₂).1 -- And.elim (fun x _ => x) (ho x₁ y₂)
        have z2 : β x₂ y₁ = 0 := (ho y₁ hy₁ x₂ hx₂).2 -- And.elim (fun _ y => y) (ho y₁ x₂)
        rw [ z1, z2 ]        
        ring
     }

  
  
