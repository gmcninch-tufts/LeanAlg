import Mathlib

variable {k V V₁ V₂ : Type} [Field k]
         [AddCommGroup V] [AddCommGroup V₁] [AddCommGroup V₂]
         [Module k V] [Module k V₁] [Module k V₂]
         
open LinearMap
open LinearMap (BilinForm)


def ProductBilinForm (β₁ : BilinForm k V₁) (β₂ : BilinForm k V₂) : 
    BilinForm k (V₁ × V₂) :=
  let γ₁ : BilinForm k (V₁ × V₂) := 
    LinearMap.compl₁₂ 
      β₁
      (LinearMap.fst k V₁ _)
      (LinearMap.fst k V₁ _)
  let γ₂ : BilinForm k (V₁ × V₂) := 
    LinearMap.compl₁₂
      β₂
      (LinearMap.snd k _ V₂)
      (LinearMap.snd k _ V₂)
  γ₁ + γ₂ 

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




--------------------------------------------------------------------------------
section DirSumBilinForm

open DirectSum
open BigOperators

variable {ι : Type} [DecidableEq ι]

variable {W : ι → Type}
         [(i : ι) → AddCommGroup (W i)]
         [(i : ι) → Module k (W i)]

example : Module k (⨁ i, W i) := inferInstance 

example (f : (j : ι) → W j →ₗ[k] V) : (⨁ i, W i) →ₗ[k] V := DirectSum.toModule k ι V f 

@[simp]
def DirSumBilinForm (φ : (i : ι) → BilinForm k (W i)) :
  BilinForm k (⨁ i, W i) := 
  let γ (j : ι) : W j →ₗ[k] (⨁ i, W i) →ₗ[k] k :=
    LinearMap.compl₁₂ 
      (φ j)
      id
      (component k ι W j)
  DirectSum.toModule k ι ((⨁ i, W i) →ₗ[k] k) γ

example (s : Finset ι) (v : (i : s) → W i) : (⨁ i, W i) := DirectSum.mk W s v
  
theorem dirsum_bilin_form_apply_single (φ : (i : ι) → BilinForm k (W i))
    (s : Finset ι) (i j : ↑s) (v : W i) (w : W j) :
  DirSumBilinForm φ (DirectSum.lof k ι W i v)
                    (DirectSum.lof k ι W j w)
  = if h : i = j  then (φ i) v (Eq.recOn h.symm w) else 0 := by   
    by_cases hh : ↑i = ↑j
    case pos => 
      simp
      rw [ hh ]
      sorry
    case neg => sorry
--    rw [ DirectSum.component.of ]
  

theorem dirsum_bilin_form_apply (φ : (i : ι) → BilinForm k (W i))
    (s : Finset ι) (v w : (i : ι) → W i) :
  DirSumBilinForm φ (DirectSum.mk W s (fun i => v i)) (DirectSum.mk W s (fun i => w i)) = 
  ∑ i ∈ s, (φ i) (v i) (w i) := by 
  simp 
  sorry 
  

  
  
end DirSumBilinForm

