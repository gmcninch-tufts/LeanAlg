import Mathlib

variable {k V V₁ V₂ : Type} [Field k]
         [AddCommGroup V] [AddCommGroup V₁] [AddCommGroup V₂]
         [Module k V] [Module k V₁] [Module k V₂]
         
open LinearMap
open LinearMap (BilinForm)



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
      subst hh
      simp_all only [DirSumBilinForm, toModule_lof, compl₁₂_apply, id_coe, id_eq, 
        component.lof_self, ↓reduceDIte]
    case neg => 
      simp [ DirectSum.component.of ]
      simp_all only [ ↓reduceDIte ]
      obtain ⟨vi, hi⟩ := i
      obtain ⟨vj, hj⟩ := j
      simp_all only [Subtype.mk.injEq]
      split
      case mk.mk.isTrue => 
        next h =>
        subst h
        simp_all only [not_true_eq_false]
      case mk.mk.isFalse =>
        next h => simp_all only [map_zero]

  

theorem dirsum_bilin_form_apply (φ : (i : ι) → BilinForm k (W i))
    (s : Finset ι) (v w : ⨁ i, W i) :
  DirSumBilinForm φ v w = 
  ∑ i ∈ s, (φ i) (DirectSum.component k ι W i v) (DirectSum.component k ι W i w) := by 
  sorry --simp
  
    -- induction (DirectSum.mk W s (fun i => v i)) using DirectSum.induction_on with
    -- | zero => simp
    -- | of => sorry
    -- | add => sorry

  
  
end DirSumBilinForm

